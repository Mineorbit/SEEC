/* automatically generated by rust-bindgen 0.60.1 */
#[allow(non_camel_case_types)]
pub type bc_sto_t = u64;
extern "C" {
    pub fn bc_to_lch(poly: *mut bc_sto_t, n_terms: ::std::os::raw::c_uint);
}
extern "C" {
    pub fn bc_to_mono(poly: *mut bc_sto_t, n_terms: ::std::os::raw::c_uint);
}
extern "C" {
    pub fn bc_to_lch_128(poly: *mut bc_sto_t, n_terms: ::std::os::raw::c_uint);
}
extern "C" {
    pub fn bc_to_mono_128(poly: *mut bc_sto_t, n_terms: ::std::os::raw::c_uint);
}
extern "C" {
    pub fn bc_to_lch_256(poly: *mut bc_sto_t, n_terms: ::std::os::raw::c_uint);
}
extern "C" {
    pub fn bc_to_mono_256(poly: *mut bc_sto_t, n_terms: ::std::os::raw::c_uint);
}
extern "C" {
    pub fn bc_to_lch_2(poly: *mut bc_sto_t, n_terms: ::std::os::raw::c_uint);
}
extern "C" {
    pub fn bc_to_mono_2(poly: *mut bc_sto_t, n_terms: ::std::os::raw::c_uint);
}
extern "C" {
    pub fn bc_to_lch_2_unit256(poly: *mut bc_sto_t, n_terms: ::std::os::raw::c_uint);
}
extern "C" {
    pub fn bc_to_mono_2_unit256(poly: *mut bc_sto_t, n_terms: ::std::os::raw::c_uint);
}