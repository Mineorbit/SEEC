use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::{digit1, multispace0};
use nom::combinator::{all_consuming, map, map_res};
use nom::error::ParseError;
use nom::multi::{count, fill};
use nom::sequence::{delimited, tuple};
use nom::IResult;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Circuit {
    header: Header,
    gates: Vec<Gate>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Header {
    gates: usize,
    wires: usize,
    /// number n1 and n2 of wires in the inputs to the function given by the circuit
    input_wires: [usize; 2],
    /// n3, number of wires in the output
    output_wires: usize,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Gate {
    And(GateData),
    Xor(GateData),
    Inv(GateData),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct GateData {
    // TODO maube use smallvecs here since these very often o
    input_wires: Vec<GateId>,
    output_wires: Vec<GateId>,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct GateId(usize);

fn integer(i: &str) -> IResult<&str, usize> {
    map_res(digit1, |s: &str| s.parse())(i)
}

fn integer_ws(i: &str) -> IResult<&str, usize> {
    ws(integer)(i)
}

fn gate_id(i: &str) -> IResult<&str, GateId> {
    map(integer_ws, GateId)(i)
}

fn header(i: &str) -> IResult<&str, Header> {
    // parse the first line of the header
    let int_ws = integer_ws;
    let (i, (gates, wires)) = tuple((int_ws, int_ws))(i)?;

    let (i, (input_wires, output_wires)) = tuple((array(int_ws), int_ws))(i)?;
    let header = Header {
        gates,
        wires,
        input_wires,
        output_wires,
    };
    Ok((i, header))
}

fn gate(i: &str) -> IResult<&str, Gate> {
    let (i, (num_in_wires, num_out_wires)) = tuple((ws(integer), ws(integer)))(i)?;
    let (i, input_wires) = count(gate_id, num_in_wires)(i)?;
    let (i, output_wires) = count(gate_id, num_out_wires)(i)?;
    let gate_data = GateData {
        input_wires,
        output_wires,
    };
    let (i, gate) = match alt((tag("AND"), tag("XOR"), tag("INV")))(i)? {
        (i, "AND") => (i, Gate::And(gate_data)),
        (i, "XOR") => (i, Gate::Xor(gate_data)),
        (i, "INV") => (i, Gate::Inv(gate_data)),
        _ => unreachable!("Bug: Parsed unknown gate"),
    };
    Ok((i, gate))
}

pub fn circuit(input: &str) -> Result<Circuit, nom::Err<nom::error::Error<&str>>> {
    let (i, header) = header(input)?;
    let (i, gates) = count(gate, header.gates)(i)?;
    let _ = all_consuming(multispace0)(i)?;
    Ok(Circuit { header, gates })
}

/// A combinator that takes a parser `inner` and produces a parser that also consumes both leading and
/// trailing whitespace, returning the output of `inner`.
/// Source: https://docs.rs/nom/latest/nom/recipes/index.html#wrapper-combinators-that-eat-whitespace-before-and-after-a-parser
fn ws<'a, F: 'a, O, E: ParseError<&'a str>>(
    inner: F,
) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
where
    F: Fn(&'a str) -> IResult<&'a str, O, E>,
{
    delimited(multispace0, inner, multispace0)
}

fn array<'a, F: 'a, O: Default + Copy, const N: usize>(
    element: F,
) -> impl FnMut(&'a str) -> IResult<&'a str, [O; N]>
where
    F: Fn(&'a str) -> IResult<&'a str, O>,
{
    move |i: &str| {
        let mut buf = [O::default(); N];
        let (i, ()) = fill(&element, &mut buf[..])(i)?;
        Ok((i, buf))
    }
}

#[cfg(test)]
mod tests {
    use crate::bristol::{circuit, gate, header, Gate, GateData, GateId, Header};
    use std::fs;

    #[test]
    fn parse_header() {
        let header_text = "33616 33872\n128 128   128";
        let parsed = header(header_text).unwrap().1;
        assert_eq!(
            Header {
                gates: 33616,
                wires: 33872,
                input_wires: [128, 128],
                output_wires: 128
            },
            parsed
        );
    }

    #[test]
    fn parse_xor_gate() {
        let gate_text = "2 1 215 87 32601 XOR";
        let parsed = gate(gate_text).unwrap().1;
        assert_eq!(
            Gate::Xor(GateData {
                input_wires: vec![GateId(215), GateId(87)],
                output_wires: vec![GateId(32601)]
            }),
            parsed
        );
    }

    #[test]
    fn parse_inv_gate() {
        let gate_text = "1 3 215 87 32601 42 INV";
        let parsed = gate(gate_text).unwrap().1;
        assert_eq!(
            Gate::Inv(GateData {
                input_wires: vec![GateId(215)],
                output_wires: vec![GateId(87), GateId(32601), GateId(42)]
            }),
            parsed
        );
    }

    #[test]
    fn parse_and_gate() {
        let gate_text = "2 1 215 87 32601 AND";
        let parsed = gate(gate_text).unwrap().1;
        assert_eq!(
            Gate::And(GateData {
                input_wires: vec![GateId(215), GateId(87)],
                output_wires: vec![GateId(32601)]
            }),
            parsed
        );
    }

    #[test]
    fn parse_aes_circuit() {
        let aes_text =
            fs::read_to_string("test_resources/bristol-circuits/AES-non-expanded.txt").unwrap();
        let parsed = circuit(&aes_text).unwrap();
        assert_eq!(33616, parsed.header.gates);
        assert_eq!(33872, parsed.header.wires);
        assert_eq!(parsed.header.gates, parsed.gates.len());
    }
}
