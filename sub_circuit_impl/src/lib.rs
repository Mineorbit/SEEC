use proc_macro::TokenStream;

use proc_macro2::Ident;
use quote::quote;
use syn::{parse_macro_input, FnArg, ItemFn, Pat, ReturnType};

#[proc_macro_attribute]
pub fn sub_circuit(_attr: TokenStream, input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as ItemFn);
    let mut inner = input.clone();
    let vis = input.vis;
    let sig = input.sig;

    inner.sig.ident = Ident::new("inner", sig.ident.span());
    let (input_idents, input_tys): (Vec<_>, Vec<_>) = inner
        .sig
        .inputs
        .iter()
        .map(|fn_arg| match fn_arg {
            FnArg::Receiver(_) => {
                panic!("self not supported")
            }
            FnArg::Typed(arg) => {
                let ident = match &*arg.pat {
                    Pat::Ident(ident) => &ident.ident,
                    _ => panic!("Unsupported pattern in function arguments"),
                };
                (ident, &*arg.ty)
            }
        })
        .unzip();

    let call_inner = quote!(inner(#(#input_idents),*));
    // the rev is important as otherwise the input gates are created in the wrong order
    let call_inner = input_idents
        .iter()
        .rev()
        .fold(call_inner, |acc, input_ident| {
            quote! {
                #input_ident.with_input(sc_id, |#input_ident| {
                    #acc
                })
            }
        });

    let inputs_size_ty = quote!((#(<#input_tys as ::gmw_rs::SubCircuitInput>::Size, )*));

    let inner_ret = match &inner.sig.output {
        ReturnType::Default => quote!(()),
        ReturnType::Type(_, ret_type) => quote!(#ret_type),
    };
    let output = quote! {
        #vis #sig {
            #inner

            use ::gmw_rs::SubCircuitInput;

            // Safety: The following is a small hack. Currently ShareWrapper explicitly don't
            // implement Send+Syn (via a PhantomData<*const  ()> because using ShareWrapper's
            // currently is unlikely to provide a performance benefit and calling #[sub_circuit]s
            // in parrallel will even result in a panic!. But we need the return type of a sub
            // circuit to be Send + Sync to store it in a static Cache. So we forcibly implement
            // Send+Sync for the wrapped return type. This is definitely safe since the
            // !Send + !Sync impl on ShareWrapper is only meant as a lint and not required for
            // safety. Furthermore, the CACHE can't even be accessed in parallel due to the
            // atomic guarding all sub circuit calls.
            struct _internal_ForceSendSync<T>(T);
            unsafe impl<T: ::gmw_rs::SubCircuitOutput> ::std::marker::Sync for _internal_ForceSendSync<T> {}
            unsafe impl<T: ::gmw_rs::SubCircuitOutput> ::std::marker::Send for _internal_ForceSendSync<T> {}

            ::gmw_rs::circuit::builder::EVALUATING_SUB_CIRCUIT
                .compare_exchange(false, true, ::std::sync::atomic::Ordering::SeqCst, ::std::sync::atomic::Ordering::SeqCst)
                .expect("Calling #[sub_circuit] functions inside each other or in parallel is currently unsupported");

            static CACHE: ::once_cell::sync::Lazy<
                ::parking_lot::Mutex<
                    ::std::collections::HashMap<
                        #inputs_size_ty,
                        (::gmw_rs::circuit::SharedCircuit, _internal_ForceSendSync<#inner_ret>)
                    >
                >
            > = ::once_cell::sync::Lazy::new(|| ::parking_lot::Mutex::new(::std::collections::HashMap::new()));

            ::gmw_rs::CircuitBuilder::with_global(|builder| {
                builder.add_cache(&*CACHE);
            });

            let input_size = (#(::gmw_rs::SubCircuitInput::size(&#input_idents),)*);
            let circ_inputs = [
                #(::gmw_rs::SubCircuitInput::flatten(#input_idents),)*
            ].concat();

            let (sc_id, ret) = match CACHE.lock().entry(input_size.clone()) {
                ::std::collections::hash_map::Entry::Vacant(entry) => {
                    let sub_circuit = ::gmw_rs::SharedCircuit::default();
                    let sc_id = ::gmw_rs::CircuitBuilder::push_global_circuit(sub_circuit.clone());
                    let ret = #call_inner;
                    let ret = ::gmw_rs::SubCircuitOutput::create_output_gates(ret);
                    entry.insert((sub_circuit, _internal_ForceSendSync(ret.clone())));
                    (sc_id, ret)
                }
                ::std::collections::hash_map::Entry::Occupied(entry) => {
                    let (sub_circuit, ret) = entry.get();
                    let sc_id = ::gmw_rs::CircuitBuilder::push_global_circuit(sub_circuit.clone());
                    (sc_id, ret.0.clone())
                }
            };
            ::gmw_rs::CircuitBuilder::with_global(|builder| {
                builder.connect_sub_circuit(&circ_inputs, sc_id);
            });


            ::gmw_rs::circuit::builder::EVALUATING_SUB_CIRCUIT
                .compare_exchange(
                    true,
                    false,
                    ::std::sync::atomic::Ordering::SeqCst,
                    ::std::sync::atomic::Ordering::SeqCst,
                ).expect("BUG: EVALUATING_SUB_CIRCUIT was false but should be true");
            ::gmw_rs::SubCircuitOutput::connect_to_main(ret, sc_id)
        }
    };
    output.into()
}
