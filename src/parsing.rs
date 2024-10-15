use crate::OmegaNum;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
/// An error that can occur when parsing an [`OmegaNum`].
pub enum FromStrError {
    /// Tried to parse with a radix that isn't base 10. Holds the base that was attempted to be parsed in.
    IncorrectRadix(u32),
    /// Encountered malformed input. Holds the index of where the parsing failed.
    MalformedInput(usize),
}

#[derive(Copy, Clone)]
pub struct ParseHead<'s> {
    input: &'s str,
    index: usize,
}

impl<'s> ParseHead<'s> {
    pub fn new(input: &'s str) -> Result<Self, FromStrError> {
        Ok(Self { input, index: 0 })
    }

    fn take(&mut self, pattern: impl FnOnce(&char) -> bool) -> Result<char, FromStrError> {
        let Some(chr) = self.input.chars().next() else {
            return Err(FromStrError::MalformedInput(self.index));
        };
        if !pattern(&chr) {
            return Err(FromStrError::MalformedInput(self.index));
        }
        let len = chr.len_utf8();
        self.input = &self.input[len..];
        self.index += len;
        Ok(chr)
    }

    fn chomp(&mut self, pattern: &str) -> Result<(), FromStrError> {
        if !self.input.starts_with(pattern) {
            return Err(FromStrError::MalformedInput(self.index));
        }
        let len = pattern.len();
        self.input = &self.input[len..];
        self.index += len;
        Ok(())
    }

    fn assert(&self, f: impl FnOnce(&str) -> bool) -> Result<(), FromStrError> {
        f(self.input)
            .then_some(())
            .ok_or(FromStrError::MalformedInput(self.index))
    }
}

impl<'s> core::ops::Deref for ParseHead<'s> {
    type Target = &'s str;

    fn deref(&self) -> &Self::Target {
        &self.input
    }
}

// Parsing rules:
// <root> ::= "NaN" | <sign>? <num>
// <sign> ::= "+" | "-"
// <num> ::= "Infinity" | "10" <opr> <float> | <float>
// <opr> ::= "^"+ | "{" <int> "}"
// <float> ::= <dec> <exp>
// <dec> ::= <int> ("." <int>)?
// <exp> ::= ("e" | "E") <sign>? <int>
// <int> ::= (NONZERO DIGIT*)

pub fn parse_omeganum(input: &mut ParseHead<'_>) -> Result<OmegaNum, FromStrError> {
    if input.chomp("NaN").is_ok() {
        input.assert(str::is_empty)?;
        return Ok(OmegaNum::NAN);
    }

    let is_negative = parse_sign(input)?;

    // <num>
    let mut res: OmegaNum = if input.chomp("Infinity").is_ok() {
        OmegaNum::INFINITY
    } else {
        'b: {
            let save = *input;
            if let Ok(num) = parse_bignum(input) {
                break 'b num;
            }
            *input = save;
            OmegaNum::from(parse_float(input)?)
        }
    };

    if is_negative {
        res.negate();
    }

    input.assert(str::is_empty)?;
    Ok(res)
}

fn parse_sign(input: &mut ParseHead<'_>) -> Result<bool, FromStrError> {
    if input.chomp("-").is_ok() {
        return Ok(true);
    }
    let _ = input.chomp("+");
    Ok(false)
}

fn parse_float(input: &mut ParseHead<'_>) -> Result<f64, FromStrError> {
    let start = **input;
    let idx = input.index;
    parse_int(input)?;
    if input.chomp(".").is_err() {
        return start[..input.index - idx]
            .parse()
            .map_err(|_| FromStrError::MalformedInput(input.index));
    }
    parse_int(input)?;
    if input.chomp("e").is_err() && input.chomp("E").is_err() {
        return start[..input.index - idx]
            .parse()
            .map_err(|_| FromStrError::MalformedInput(input.index));
    }
    parse_sign(input)?;
    parse_int(input)?;
    start[..input.index - idx]
        .parse()
        .map_err(|_| FromStrError::MalformedInput(input.index))
}

fn parse_bignum(input: &mut ParseHead<'_>) -> Result<OmegaNum, FromStrError> {
    input.chomp("10")?;
    let arrow_count = parse_operator(input)?;
    let base = parse_float(input)?;
    Ok(OmegaNum::from_arrows(base, arrow_count))
}

fn parse_operator(input: &mut ParseHead<'_>) -> Result<usize, FromStrError> {
    if input.chomp("^").is_ok() {
        let mut count = 1;
        while input.starts_with('^') {
            input.chomp("^")?;
            count += 1;
        }
        Ok(count)
    } else {
        input.chomp("{")?;
        let count = parse_int(input)?;
        input.chomp("}")?;
        Ok(count)
    }
}

fn parse_int(input: &mut ParseHead<'_>) -> Result<usize, FromStrError> {
    if input.chomp("0").is_ok() {
        return Ok(0);
    }
    let mut count: usize = input
        .take(char::is_ascii_digit)?
        .to_digit(10)
        .ok_or(FromStrError::MalformedInput(input.index))? as usize;
    while let Some(c) = input
        .take(char::is_ascii_digit)
        .ok()
        .and_then(|c| c.to_digit(10))
    {
        count = count.saturating_mul(10).saturating_add(c as usize);
    }
    Ok(count)
}
