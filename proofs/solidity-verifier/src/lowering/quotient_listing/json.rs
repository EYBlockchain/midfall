// SPDX-License-Identifier: CC0-1.0
//! Minimal deterministic JSON writer for the quotient manifest.
//!
//! The crate has no serde dependency; the manifest only needs objects with
//! ordered keys, arrays, strings, booleans, null and unsigned integers.

/// JSON value with insertion-ordered object keys.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Json {
    /// `null`.
    Null,
    /// `true` / `false`.
    Bool(bool),
    /// Unsigned integer.
    Num(u64),
    /// String.
    Str(String),
    /// Array.
    Arr(Vec<Json>),
    /// Object with ordered keys.
    Obj(Vec<(String, Json)>),
}

impl Json {
    /// String value.
    pub(crate) fn str(value: impl Into<String>) -> Self {
        Self::Str(value.into())
    }

    /// Unsigned integer value.
    pub(crate) fn num(value: usize) -> Self {
        Self::Num(value as u64)
    }

    /// Hex string `0x...` for an address or offset.
    pub(crate) fn hex(value: usize) -> Self {
        Self::Str(format!("{value:#x}"))
    }

    /// Object from key/value pairs.
    pub(crate) fn obj<const N: usize>(pairs: [(&str, Json); N]) -> Self {
        Self::Obj(pairs.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
    }

    /// Pretty-print with two-space indentation; arrays of scalars stay on one
    /// line.
    pub(crate) fn pretty(&self) -> String {
        let mut out = String::new();
        self.write(&mut out, 0);
        out.push('\n');
        out
    }

    /// Whether the value is a scalar (not an array or object).
    fn is_scalar(&self) -> bool {
        !matches!(self, Self::Arr(_) | Self::Obj(_))
    }

    /// Recursive writer.
    fn write(&self, out: &mut String, indent: usize) {
        match self {
            Self::Null => out.push_str("null"),
            Self::Bool(value) => out.push_str(if *value { "true" } else { "false" }),
            Self::Num(value) => out.push_str(&value.to_string()),
            Self::Str(value) => write_string(out, value),
            Self::Arr(values) => {
                if values.is_empty() {
                    out.push_str("[]");
                } else if values.iter().all(Self::is_scalar) {
                    out.push('[');
                    for (idx, value) in values.iter().enumerate() {
                        if idx > 0 {
                            out.push_str(", ");
                        }
                        value.write(out, indent);
                    }
                    out.push(']');
                } else {
                    out.push_str("[\n");
                    for (idx, value) in values.iter().enumerate() {
                        push_indent(out, indent + 1);
                        value.write(out, indent + 1);
                        if idx + 1 < values.len() {
                            out.push(',');
                        }
                        out.push('\n');
                    }
                    push_indent(out, indent);
                    out.push(']');
                }
            }
            Self::Obj(pairs) => {
                if pairs.is_empty() {
                    out.push_str("{}");
                    return;
                }
                out.push_str("{\n");
                for (idx, (key, value)) in pairs.iter().enumerate() {
                    push_indent(out, indent + 1);
                    write_string(out, key);
                    out.push_str(": ");
                    value.write(out, indent + 1);
                    if idx + 1 < pairs.len() {
                        out.push(',');
                    }
                    out.push('\n');
                }
                push_indent(out, indent);
                out.push('}');
            }
        }
    }
}

/// Append `indent` levels of two-space indentation.
fn push_indent(out: &mut String, indent: usize) {
    for _ in 0..indent {
        out.push_str("  ");
    }
}

/// Append a JSON string literal with RFC 8259 escaping.
fn write_string(out: &mut String, value: &str) {
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

#[cfg(test)]
mod tests {
    use super::Json;

    #[test]
    fn json_writer_escapes_and_orders_keys() {
        let value = Json::obj([
            ("b", Json::num(2)),
            ("a", Json::str("x\"y\\z\n")),
            (
                "list",
                Json::Arr(vec![Json::num(1), Json::Bool(true), Json::Null]),
            ),
            (
                "nested",
                Json::Arr(vec![Json::obj([("k", Json::hex(255))])]),
            ),
        ]);
        assert_eq!(
            value.pretty(),
            "{\n  \"b\": 2,\n  \"a\": \"x\\\"y\\\\z\\n\",\n  \"list\": [1, true, null],\n  \"nested\": [\n    {\n      \"k\": \"0xff\"\n    }\n  ]\n}\n"
        );
    }
}
