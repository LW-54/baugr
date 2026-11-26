//! Data-driven `ERG-L2` Promise Schema Registry, Layer-1 -> Layer-0 Total Desugaring,
//! Static Payload Validation, and JSON Schema (Draft 2020-12) Generation.
//!
//! 100% usage-agnostic, zero `std::fs`, zero domain strings. Every shorthand manifest
//! desugars totally and deterministically into the exact Layer-0 [`AgentManifest`] AST
//! verified by the Lean 4 specification (`lean/Baugr/*`).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use serde::{Deserialize, Serialize};
use serde_json::{Map, Value, json};

use crate::agency::{Cardinality, Polarity, SoftContract, Strength};
use crate::attr_expr::AttrExpr;
use crate::fleet::{AgentManifest, ChildRef, FleetSpec, PromiseSpec};

/// Primitive JSON value type for typed payload fields in `schemas/*.toml`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FieldType {
    /// UTF-8 string value.
    String,
    /// Integer value (signed or unsigned, no fractional part).
    Integer,
    /// Any finite JSON number.
    Number,
    /// Boolean value.
    Boolean,
    /// JSON array value.
    Array,
    /// Nested JSON object value.
    Object,
    /// Unconstrained JSON value.
    #[default]
    Any,
}

impl FieldType {
    /// Returns the JSON Schema `"type"` keyword for this field type (`None` for [`Self::Any`]).
    #[must_use]
    pub const fn json_schema_type(self) -> Option<&'static str> {
        match self {
            Self::String => Some("string"),
            Self::Integer => Some("integer"),
            Self::Number => Some("number"),
            Self::Boolean => Some("boolean"),
            Self::Array => Some("array"),
            Self::Object => Some("object"),
            Self::Any => None,
        }
    }

    /// Returns `true` iff `value` conforms to this primitive field type.
    #[must_use]
    pub fn matches(self, value: &Value) -> bool {
        match self {
            Self::String => value.is_string(),
            Self::Integer => value.is_i64() || value.is_u64(),
            Self::Number => value.is_number(),
            Self::Boolean => value.is_boolean(),
            Self::Array => value.is_array(),
            Self::Object => value.is_object(),
            Self::Any => true,
        }
    }
}

/// Returns the human-readable JSON type label of a runtime [`Value`].
#[must_use]
pub fn json_value_type_name(value: &Value) -> &'static str {
    match value {
        Value::Null => "null",
        Value::Bool(_) => "boolean",
        Value::Number(n) if n.is_i64() || n.is_u64() => "integer",
        Value::Number(_) => "number",
        Value::String(_) => "string",
        Value::Array(_) => "array",
        Value::Object(_) => "object",
    }
}

/// Schema specification for a single payload field inside `[promises.<ptype>.payload]`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FieldSchema {
    /// Expected JSON value type.
    #[serde(rename = "type", default)]
    pub field_type: FieldType,
    /// Whether offers of this promise type must supply this payload field.
    #[serde(default)]
    pub required: bool,
    /// Human-readable field documentation.
    #[serde(default)]
    pub description: String,
}

/// Data-driven schema entry for a promise contract type (`τ`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PromiseSchema {
    /// Human-readable contract description.
    #[serde(default)]
    pub description: String,
    /// Default `B3` binding cardinality when omitted in shorthand or raw manifests.
    #[serde(default = "default_exclusive")]
    pub cardinality: Cardinality,
    /// When `true`, `[offer.<ptype>]` and `[use.<ptype>]` are maps of `<key> -> entry`.
    /// When `false`, `[offer.<ptype>]` is a single promise entry whose default key is `<ptype>`.
    #[serde(default)]
    pub keyed: bool,
    /// Default `mandatory` flag for `Offer` (`+b`) promises (defaults to `true`).
    #[serde(default = "default_true")]
    pub default_offer_mandatory: bool,
    /// Default `mandatory` flag for `Use` (`-b`) promises (defaults to `true`).
    #[serde(default = "default_true")]
    pub default_use_mandatory: bool,
    /// Default `strength` (`Hard` or `Soft`; defaults to `Hard`).
    #[serde(default = "default_hard")]
    pub default_strength: Strength,
    /// Default priority tier (`0` = critical; defaults to `1`).
    #[serde(default = "default_priority")]
    pub default_priority: u64,
    /// Default acyclic stratification rank (defaults to `0`).
    #[serde(default)]
    pub default_stratum: u64,
    /// Base tags automatically merged onto `Offer` (`+b`) promises (deduplicated).
    #[serde(default)]
    pub default_tags: Vec<String>,
    /// Optional payload field used to derive `key` if `key` is omitted.
    #[serde(default)]
    pub key_from_payload: Option<String>,
    /// Typed payload field constraints checked statically on `Offer` (`+b`) promises.
    #[serde(default)]
    pub payload: BTreeMap<String, FieldSchema>,
}

impl Default for PromiseSchema {
    fn default() -> Self {
        Self {
            description: String::new(),
            cardinality: Cardinality::Exclusive,
            keyed: false,
            default_offer_mandatory: true,
            default_use_mandatory: true,
            default_strength: Strength::Hard,
            default_priority: 1,
            default_stratum: 0,
            default_tags: Vec::new(),
            key_from_payload: None,
            payload: BTreeMap::new(),
        }
    }
}

/// Complete promise schema catalog merged across all `--root` `schemas/*.toml` overlays.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SchemaCatalog {
    /// When `true`, every promise `ptype` in the fleet must be declared in [`Self::promises`].
    #[serde(default)]
    pub strict: bool,
    /// Map of `ptype -> PromiseSchema`.
    #[serde(default)]
    pub promises: BTreeMap<String, PromiseSchema>,
}

impl SchemaCatalog {
    /// Merges another schema catalog overlay into `self` (later roots override matching `ptype`s).
    pub fn merge(&mut self, other: Self) {
        self.strict = self.strict || other.strict;
        for (ptype, schema) in other.promises {
            self.promises.insert(ptype, schema);
        }
    }
}

/// Structured or string-shorthand `AttrExpr` accepted in Layer-1 manifests.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum RawSelector {
    /// String shorthand: `"*"` -> [`AttrExpr::Any`], any other tag -> [`AttrExpr::Atom`].
    Shorthand(String),
    /// Structured boolean expression (children may also use string shorthand).
    Structured(RawAttrExpr),
}

/// Structured boolean set-algebra `AttrExpr` AST allowing nested string shorthands.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
pub enum RawAttrExpr {
    /// Matches every tag set.
    Any,
    /// Empty predicate matching no tag set.
    #[serde(rename = "none")]
    NoneExpr,
    /// Matches iff `tag` is present.
    Atom {
        /// Required tag.
        tag: String,
    },
    /// Logical complement (`¬ inner`).
    Compl {
        /// Negated sub-expression.
        inner: Box<RawSelector>,
    },
    /// Logical conjunction / intersection (`left ∩ right`).
    Inter {
        /// Left operand.
        left: Box<RawSelector>,
        /// Right operand.
        right: Box<RawSelector>,
    },
    /// Logical disjunction / union (`left ∪ right`).
    Union {
        /// Left operand.
        left: Box<RawSelector>,
        /// Right operand.
        right: Box<RawSelector>,
    },
    /// Set difference (`left \ right`).
    Diff {
        /// Included operand.
        left: Box<RawSelector>,
        /// Excluded operand.
        right: Box<RawSelector>,
    },
}

impl RawSelector {
    /// Totally lowers a Layer-1 selector into the canonical Layer-0 [`AttrExpr`].
    #[must_use]
    pub fn into_attr_expr(self) -> AttrExpr {
        match self {
            Self::Shorthand(s) if s == "*" => AttrExpr::Any,
            Self::Shorthand(tag) => AttrExpr::Atom { tag },
            Self::Structured(expr) => match expr {
                RawAttrExpr::Any => AttrExpr::Any,
                RawAttrExpr::NoneExpr => AttrExpr::NoneExpr,
                RawAttrExpr::Atom { tag } => AttrExpr::Atom { tag },
                RawAttrExpr::Compl { inner } => AttrExpr::Compl {
                    inner: Box::new(inner.into_attr_expr()),
                },
                RawAttrExpr::Inter { left, right } => AttrExpr::Inter {
                    left: Box::new(left.into_attr_expr()),
                    right: Box::new(right.into_attr_expr()),
                },
                RawAttrExpr::Union { left, right } => AttrExpr::Union {
                    left: Box::new(left.into_attr_expr()),
                    right: Box::new(right.into_attr_expr()),
                },
                RawAttrExpr::Diff { left, right } => AttrExpr::Diff {
                    left: Box::new(left.into_attr_expr()),
                    right: Box::new(right.into_attr_expr()),
                },
            },
        }
    }
}

/// Layer-1 raw promise declaration inside `[[promises]]` or `[[internal_promises]]`.
///
/// Backwards-compatible superset of Layer-0 [`PromiseSpec`] where omitted fields inherit
/// defaults from [`SchemaCatalog`] (or standard Layer-0 defaults when no schema matches).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RawPromiseSpec {
    /// Promise contract type (`τ`).
    pub ptype: String,
    /// Optional explicit key (defaults to `schema.key_from_payload` or `ptype`).
    #[serde(default)]
    pub key: Option<String>,
    /// Offer (`+b`) or Use (`-b`).
    pub polarity: Polarity,
    /// Static `Hard` or conditional `Soft`.
    #[serde(default)]
    pub strength: Option<Strength>,
    /// `B3` binding cardinality.
    #[serde(default)]
    pub cardinality: Option<Cardinality>,
    /// Whether an unbound `Hard` promise fails verification.
    #[serde(default)]
    pub mandatory: Option<bool>,
    /// Quantitative resource amount for `Budgeted` promises.
    #[serde(default)]
    pub amount: u64,
    /// Priority tier (`0` = critical survival tier).
    #[serde(default)]
    pub priority: Option<u64>,
    /// Acyclic stratification rank.
    #[serde(default)]
    pub stratum: Option<u64>,
    /// Expressed tags for routing and declarative invariants.
    #[serde(default)]
    pub tags: Vec<String>,
    /// `AttrExpr` selector for consumers (accepts string shorthand or structured form).
    #[serde(default)]
    pub selector: Option<RawSelector>,
    /// Mandatory metadata when `strength == Strength::Soft`.
    #[serde(default)]
    pub soft: Option<SoftContract>,
    /// Optional fallback payload when a `-b` Use is optional and unbound.
    #[serde(default)]
    pub default: Option<Value>,
    /// Arbitrary typed data payload carried across `Σ` by `+b` Offers.
    #[serde(default)]
    pub payload: BTreeMap<String, Value>,
}

/// Layer-1 child reference inside `contains = [ ... ]`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum RawChildRef {
    /// Concise string shorthand: `"child-id"`.
    Id(String),
    /// Detailed child reference supporting `instance` and child-scoped promises/shorthands.
    Detailed(Box<RawChildRefDetailed>),
}

/// Detailed form of [`RawChildRef`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RawChildRefDetailed {
    /// Referenced agent ID.
    pub agent: String,
    /// Optional local instance alias for multi-instance instantiation.
    #[serde(default)]
    pub instance: Option<String>,
    /// Raw child-scoped promises.
    #[serde(default)]
    pub promises: Vec<RawPromiseSpec>,
    /// Shorthand child-scoped `+b` offers.
    #[serde(default)]
    pub offer: BTreeMap<String, Value>,
    /// Shorthand child-scoped `-b` uses.
    #[serde(default, rename = "use")]
    pub uses: BTreeMap<String, Value>,
}

/// Interior shorthand tables `[internal.offer]` and `[internal.use]`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RawInternalSection {
    /// Interior-only `+b` offers scoped strictly inside this superagent.
    #[serde(default)]
    pub offer: BTreeMap<String, Value>,
    /// Interior-only `-b` uses scoped strictly inside this superagent.
    #[serde(default, rename = "use")]
    pub uses: BTreeMap<String, Value>,
}

/// Layer-1 Agent manifest parsed from `agent.toml` before total desugaring into [`AgentManifest`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RawAgentManifest {
    /// Unique agent identifier.
    pub id: String,
    /// Human-readable description.
    #[serde(default)]
    pub description: String,
    /// Factual entity attributes (`EXPRESSES` tags).
    #[serde(default)]
    pub attributes: Vec<String>,
    /// Transparent profiles (`P-Dual`) flattened into this superagent's interior.
    #[serde(default)]
    pub profiles: Vec<String>,
    /// Direct child agents (`"child"` or `{ agent = "...", ... }`).
    #[serde(default)]
    pub contains: Vec<RawChildRef>,
    /// Raw Layer-0 interior-only promises.
    #[serde(default)]
    pub internal_promises: Vec<RawPromiseSpec>,
    /// Raw Layer-0 exterior promises.
    #[serde(default)]
    pub promises: Vec<RawPromiseSpec>,
    /// Shorthand exterior `+b` offers (`[offer.<ptype>]` or `[offer.<ptype>.<key>]`).
    #[serde(default)]
    pub offer: BTreeMap<String, Value>,
    /// Shorthand exterior `-b` uses (`[use.<ptype>]` or `[use.<ptype>.<key>]`).
    #[serde(default, rename = "use")]
    pub uses: BTreeMap<String, Value>,
    /// Shorthand interior promises (`[internal.offer.*]` / `[internal.use.*]`).
    #[serde(default)]
    pub internal: RawInternalSection,
}

/// Deterministic error returned when a Layer-1 shorthand manifest is malformed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DesugarError {
    /// A schema with `keyed = true` received a non-table value at `[offer.<ptype>]` or `[use.<ptype>]`.
    ExpectedKeyedMap {
        /// Agent identifier.
        agent_id: String,
        /// Promise type.
        ptype: String,
    },
    /// Invalid scalar/array shorthand entry (e.g., `false` or numeric amount on non-budgeted promise).
    InvalidShorthandEntry {
        /// Agent identifier.
        agent_id: String,
        /// Promise type.
        ptype: String,
        /// Human-readable reason.
        reason: String,
    },
    /// A reserved promise metadata field inside a shorthand table failed to parse.
    InvalidMetaField {
        /// Agent identifier.
        agent_id: String,
        /// Promise type.
        ptype: String,
        /// Metadata field name.
        field: String,
        /// Parse error message.
        reason: String,
    },
    /// A key was supplied both inline in the shorthand table and inside `payload = { ... }`.
    DuplicatePayloadField {
        /// Agent identifier.
        agent_id: String,
        /// Promise type.
        ptype: String,
        /// Colliding payload field name.
        field: String,
    },
}

impl fmt::Display for DesugarError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExpectedKeyedMap { agent_id, ptype } => write!(
                f,
                "agent `{agent_id}` promise `{ptype}` is schema-declared `keyed = true` and requires a `<key> = {{ ... }}` map"
            ),
            Self::InvalidShorthandEntry {
                agent_id,
                ptype,
                reason,
            } => write!(
                f,
                "agent `{agent_id}` invalid shorthand entry for `{ptype}`: {reason}"
            ),
            Self::InvalidMetaField {
                agent_id,
                ptype,
                field,
                reason,
            } => write!(
                f,
                "agent `{agent_id}` invalid `{field}` on `{ptype}`: {reason}"
            ),
            Self::DuplicatePayloadField {
                agent_id,
                ptype,
                field,
            } => write!(
                f,
                "agent `{agent_id}` duplicate payload field `{field}` on `{ptype}` (both inline and in `payload`)"
            ),
        }
    }
}

impl std::error::Error for DesugarError {}

/// Static schema validation violation discovered by [`validate_fleet_schemas`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SchemaError {
    /// Strict schema mode rejected an undeclared promise type (`ptype`).
    UnknownPromiseType {
        /// Agent identifier.
        agent_id: String,
        /// Undeclared promise type.
        ptype: String,
    },
    /// An offer omitted a required payload field declared in `schemas/*.toml`.
    MissingRequiredField {
        /// Agent identifier.
        agent_id: String,
        /// Promise type.
        ptype: String,
        /// Promise key.
        key: String,
        /// Missing payload field name.
        field: String,
    },
    /// An offer supplied a payload field whose JSON value type violates `schemas/*.toml`.
    InvalidFieldType {
        /// Agent identifier.
        agent_id: String,
        /// Promise type.
        ptype: String,
        /// Promise key.
        key: String,
        /// Payload field name.
        field: String,
        /// Expected schema type.
        expected: FieldType,
        /// Observed JSON type label.
        actual: String,
    },
}

/// Target document kind for [`generate_json_schema`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SchemaKind {
    /// JSON Schema for `agent.toml` (dynamically specialized to loaded `schemas/*.toml`).
    Agent,
    /// JSON Schema for `profiles/*.toml`.
    Profile,
    /// JSON Schema for `policies/*.toml`.
    Policy,
    /// JSON Schema for `schemas/*.toml` itself.
    Schema,
}

const fn default_exclusive() -> Cardinality {
    Cardinality::Exclusive
}

const fn default_true() -> bool {
    true
}

const fn default_hard() -> Strength {
    Strength::Hard
}

const fn default_priority() -> u64 {
    1
}

fn merge_tags(base: &[String], extra: &[String]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for t in base.iter().chain(extra.iter()) {
        if seen.insert(t.clone()) {
            out.push(t.clone());
        }
    }
    out
}

fn resolve_default_key(
    ptype: &str,
    explicit_key: Option<String>,
    payload: &BTreeMap<String, Value>,
    schema: Option<&PromiseSchema>,
) -> String {
    if let Some(k) = explicit_key {
        return k;
    }
    if let Some(field_name) = schema.and_then(|s| s.key_from_payload.as_deref())
        && let Some(Value::String(derived)) = payload.get(field_name)
    {
        return derived.clone();
    }
    ptype.to_string()
}

fn desugar_raw_promise(raw: RawPromiseSpec, schemas: &SchemaCatalog) -> PromiseSpec {
    let schema = schemas.promises.get(&raw.ptype);
    let cardinality = raw
        .cardinality
        .or_else(|| schema.map(|s| s.cardinality))
        .unwrap_or(Cardinality::Exclusive);
    let mandatory = raw.mandatory.unwrap_or_else(|| {
        schema.is_none_or(|s| match raw.polarity {
            Polarity::Offer => s.default_offer_mandatory,
            Polarity::Use => s.default_use_mandatory,
        })
    });
    let strength = raw
        .strength
        .or_else(|| schema.map(|s| s.default_strength))
        .unwrap_or(Strength::Hard);
    let priority = raw
        .priority
        .or_else(|| schema.map(|s| s.default_priority))
        .unwrap_or(1);
    let stratum = raw
        .stratum
        .or_else(|| schema.map(|s| s.default_stratum))
        .unwrap_or(0);
    let tags = match raw.polarity {
        Polarity::Offer => schema.map_or_else(
            || raw.tags.clone(),
            |s| merge_tags(&s.default_tags, &raw.tags),
        ),
        Polarity::Use => raw.tags,
    };
    let key = resolve_default_key(&raw.ptype, raw.key, &raw.payload, schema);
    let selector = raw
        .selector
        .map_or(AttrExpr::Any, RawSelector::into_attr_expr);

    PromiseSpec {
        ptype: raw.ptype,
        key,
        polarity: raw.polarity,
        strength,
        cardinality,
        mandatory,
        amount: raw.amount,
        priority,
        stratum,
        tags,
        selector,
        soft: raw.soft,
        default: raw.default,
        payload: raw.payload,
    }
}

fn parse_meta<T: serde::de::DeserializeOwned>(
    agent_id: &str,
    ptype: &str,
    field: &str,
    value: Value,
) -> Result<T, DesugarError> {
    serde_json::from_value(value).map_err(|err| DesugarError::InvalidMetaField {
        agent_id: agent_id.to_string(),
        ptype: ptype.to_string(),
        field: field.to_string(),
        reason: err.to_string(),
    })
}

fn desugar_shorthand_entry(
    agent_id: &str,
    ptype: &str,
    map_key: Option<&str>,
    polarity: Polarity,
    entry: Value,
    schemas: &SchemaCatalog,
) -> Result<PromiseSpec, DesugarError> {
    let schema = schemas.promises.get(ptype);
    let default_card = schema.map_or(Cardinality::Exclusive, |s| s.cardinality);

    match entry {
        Value::Bool(true) => Ok(desugar_raw_promise(
            RawPromiseSpec {
                ptype: ptype.to_string(),
                key: map_key.map(ToString::to_string),
                polarity,
                strength: None,
                cardinality: None,
                mandatory: None,
                amount: 0,
                priority: None,
                stratum: None,
                tags: Vec::new(),
                selector: None,
                soft: None,
                default: None,
                payload: BTreeMap::new(),
            },
            schemas,
        )),
        Value::Bool(false) => Err(DesugarError::InvalidShorthandEntry {
            agent_id: agent_id.to_string(),
            ptype: ptype.to_string(),
            reason:
                "boolean `false` is disallowed; omit the promise or use `{ mandatory = false }`"
                    .to_string(),
        }),
        Value::Number(num) if default_card == Cardinality::Budgeted => {
            let Some(amount) = num.as_u64() else {
                return Err(DesugarError::InvalidShorthandEntry {
                    agent_id: agent_id.to_string(),
                    ptype: ptype.to_string(),
                    reason: "budgeted numeric shorthand must be a non-negative integer".to_string(),
                });
            };
            Ok(desugar_raw_promise(
                RawPromiseSpec {
                    ptype: ptype.to_string(),
                    key: map_key.map(ToString::to_string),
                    polarity,
                    strength: None,
                    cardinality: Some(Cardinality::Budgeted),
                    mandatory: None,
                    amount,
                    priority: None,
                    stratum: None,
                    tags: Vec::new(),
                    selector: None,
                    soft: None,
                    default: None,
                    payload: BTreeMap::new(),
                },
                schemas,
            ))
        }
        Value::Object(obj) => {
            desugar_shorthand_object(agent_id, ptype, map_key, polarity, obj, schemas)
        }
        other => Err(DesugarError::InvalidShorthandEntry {
            agent_id: agent_id.to_string(),
            ptype: ptype.to_string(),
            reason: format!(
                "expected `true`, a table, or an integer (for budgeted promises), found {}",
                json_value_type_name(&other)
            ),
        }),
    }
}

fn desugar_shorthand_object(
    agent_id: &str,
    ptype: &str,
    map_key: Option<&str>,
    polarity: Polarity,
    obj: Map<String, Value>,
    schemas: &SchemaCatalog,
) -> Result<PromiseSpec, DesugarError> {
    let mut explicit_key: Option<String> = map_key.map(ToString::to_string);
    let mut strength: Option<Strength> = None;
    let mut cardinality: Option<Cardinality> = None;
    let mut mandatory: Option<bool> = None;
    let mut amount: u64 = 0;
    let mut priority: Option<u64> = None;
    let mut stratum: Option<u64> = None;
    let mut tags: Vec<String> = Vec::new();
    let mut selector: Option<RawSelector> = None;
    let mut soft: Option<SoftContract> = None;
    let mut default: Option<Value> = None;
    let mut explicit_payload: Option<BTreeMap<String, Value>> = None;
    let mut inline_payload: BTreeMap<String, Value> = BTreeMap::new();

    for (k, v) in obj {
        match k.as_str() {
            "key" => explicit_key = Some(parse_meta(agent_id, ptype, "key", v)?),
            "strength" => strength = Some(parse_meta(agent_id, ptype, "strength", v)?),
            "cardinality" => cardinality = Some(parse_meta(agent_id, ptype, "cardinality", v)?),
            "mandatory" => mandatory = Some(parse_meta(agent_id, ptype, "mandatory", v)?),
            "amount" => amount = parse_meta(agent_id, ptype, "amount", v)?,
            "priority" => priority = Some(parse_meta(agent_id, ptype, "priority", v)?),
            "stratum" => stratum = Some(parse_meta(agent_id, ptype, "stratum", v)?),
            "tags" => tags = parse_meta(agent_id, ptype, "tags", v)?,
            "selector" => selector = Some(parse_meta(agent_id, ptype, "selector", v)?),
            "soft" => soft = Some(parse_meta(agent_id, ptype, "soft", v)?),
            "default" => default = Some(v),
            "payload" => explicit_payload = Some(parse_meta(agent_id, ptype, "payload", v)?),
            _ => {
                inline_payload.insert(k, v);
            }
        }
    }

    let mut payload = inline_payload;
    if let Some(ep) = explicit_payload {
        for (pk, pv) in ep {
            if payload.contains_key(&pk) {
                return Err(DesugarError::DuplicatePayloadField {
                    agent_id: agent_id.to_string(),
                    ptype: ptype.to_string(),
                    field: pk,
                });
            }
            payload.insert(pk, pv);
        }
    }

    Ok(desugar_raw_promise(
        RawPromiseSpec {
            ptype: ptype.to_string(),
            key: explicit_key,
            polarity,
            strength,
            cardinality,
            mandatory,
            amount,
            priority,
            stratum,
            tags,
            selector,
            soft,
            default,
            payload,
        },
        schemas,
    ))
}

fn desugar_shorthand_map(
    agent_id: &str,
    map: BTreeMap<String, Value>,
    polarity: Polarity,
    schemas: &SchemaCatalog,
) -> Result<Vec<PromiseSpec>, DesugarError> {
    let mut out = Vec::new();
    for (ptype, val) in map {
        let is_keyed = schemas.promises.get(&ptype).is_some_and(|s| s.keyed);
        if is_keyed {
            let Value::Object(key_entries) = val else {
                return Err(DesugarError::ExpectedKeyedMap {
                    agent_id: agent_id.to_string(),
                    ptype,
                });
            };
            let sorted: BTreeMap<String, Value> = key_entries.into_iter().collect();
            for (k, entry) in sorted {
                out.push(desugar_shorthand_entry(
                    agent_id,
                    &ptype,
                    Some(&k),
                    polarity,
                    entry,
                    schemas,
                )?);
            }
        } else {
            out.push(desugar_shorthand_entry(
                agent_id, &ptype, None, polarity, val, schemas,
            )?);
        }
    }
    Ok(out)
}

/// Totally lowers a Layer-1 [`RawAgentManifest`] into a pure Layer-0 [`AgentManifest`].
///
/// # Errors
///
/// Returns [`DesugarError`] if a shorthand entry violates its structural shape (e.g., passing a
/// non-map to a `keyed = true` promise type or supplying invalid reserved metadata).
pub fn desugar_agent(
    raw: RawAgentManifest,
    schemas: &SchemaCatalog,
) -> Result<AgentManifest, DesugarError> {
    let agent_id = raw.id.clone();

    let mut promises: Vec<PromiseSpec> = raw
        .promises
        .into_iter()
        .map(|p| desugar_raw_promise(p, schemas))
        .collect();
    promises.extend(desugar_shorthand_map(
        &agent_id,
        raw.offer,
        Polarity::Offer,
        schemas,
    )?);
    promises.extend(desugar_shorthand_map(
        &agent_id,
        raw.uses,
        Polarity::Use,
        schemas,
    )?);

    let mut internal_promises: Vec<PromiseSpec> = raw
        .internal_promises
        .into_iter()
        .map(|p| desugar_raw_promise(p, schemas))
        .collect();
    internal_promises.extend(desugar_shorthand_map(
        &agent_id,
        raw.internal.offer,
        Polarity::Offer,
        schemas,
    )?);
    internal_promises.extend(desugar_shorthand_map(
        &agent_id,
        raw.internal.uses,
        Polarity::Use,
        schemas,
    )?);

    let mut contains = Vec::with_capacity(raw.contains.len());
    for ch in raw.contains {
        match ch {
            RawChildRef::Id(agent) => contains.push(ChildRef {
                agent,
                instance: None,
                promises: Vec::new(),
            }),
            RawChildRef::Detailed(det) => {
                let mut child_ps: Vec<PromiseSpec> = det
                    .promises
                    .into_iter()
                    .map(|p| desugar_raw_promise(p, schemas))
                    .collect();
                child_ps.extend(desugar_shorthand_map(
                    &agent_id,
                    det.offer,
                    Polarity::Offer,
                    schemas,
                )?);
                child_ps.extend(desugar_shorthand_map(
                    &agent_id,
                    det.uses,
                    Polarity::Use,
                    schemas,
                )?);
                contains.push(ChildRef {
                    agent: det.agent,
                    instance: det.instance,
                    promises: child_ps,
                });
            }
        }
    }

    Ok(AgentManifest {
        id: raw.id,
        description: raw.description,
        attributes: raw.attributes,
        profiles: raw.profiles,
        contains,
        internal_promises,
        promises,
    })
}

fn validate_promise_against_schema(
    agent_id: &str,
    p: &PromiseSpec,
    schemas: &SchemaCatalog,
    errors: &mut Vec<SchemaError>,
) {
    let Some(pschema) = schemas.promises.get(&p.ptype) else {
        if schemas.strict {
            errors.push(SchemaError::UnknownPromiseType {
                agent_id: agent_id.to_string(),
                ptype: p.ptype.clone(),
            });
        }
        return;
    };

    if p.polarity == Polarity::Offer {
        for (field_name, fschema) in &pschema.payload {
            match p.payload.get(field_name) {
                None if fschema.required => {
                    errors.push(SchemaError::MissingRequiredField {
                        agent_id: agent_id.to_string(),
                        ptype: p.ptype.clone(),
                        key: p.key.clone(),
                        field: field_name.clone(),
                    });
                }
                Some(val) if !fschema.field_type.matches(val) => {
                    errors.push(SchemaError::InvalidFieldType {
                        agent_id: agent_id.to_string(),
                        ptype: p.ptype.clone(),
                        key: p.key.clone(),
                        field: field_name.clone(),
                        expected: fschema.field_type,
                        actual: json_value_type_name(val).to_string(),
                    });
                }
                _ => {}
            }
        }
    }
}

/// Validates every promise in `fleet` against `schemas` (unknown `ptype` in strict mode,
/// required offer payload fields, and primitive payload field types).
#[must_use]
pub fn validate_fleet_schemas(fleet: &FleetSpec, schemas: &SchemaCatalog) -> Vec<SchemaError> {
    if !schemas.strict && schemas.promises.is_empty() {
        return Vec::new();
    }
    let mut errors = Vec::new();
    for (aid, agent) in &fleet.agents {
        for p in agent
            .promises
            .iter()
            .chain(agent.internal_promises.iter())
            .chain(agent.contains.iter().flat_map(|c| c.promises.iter()))
        {
            validate_promise_against_schema(aid, p, schemas, &mut errors);
        }
    }
    errors
}

fn field_schema_to_json(fs: &FieldSchema) -> Value {
    let mut obj = Map::new();
    if let Some(ty) = fs.field_type.json_schema_type() {
        obj.insert("type".to_string(), Value::String(ty.to_string()));
    }
    if !fs.description.is_empty() {
        obj.insert(
            "description".to_string(),
            Value::String(fs.description.clone()),
        );
    }
    Value::Object(obj)
}

fn promise_entry_json_schema(ps: &PromiseSchema, is_offer: bool) -> Value {
    let mut props = Map::new();
    props.insert("key".to_string(), json!({ "type": "string" }));
    props.insert(
        "strength".to_string(),
        json!({ "type": "string", "enum": ["hard", "soft"] }),
    );
    props.insert(
        "cardinality".to_string(),
        json!({ "type": "string", "enum": ["exclusive", "broadcast", "partitioned", "budgeted"] }),
    );
    props.insert("mandatory".to_string(), json!({ "type": "boolean" }));
    props.insert(
        "amount".to_string(),
        json!({ "type": "integer", "minimum": 0 }),
    );
    props.insert(
        "priority".to_string(),
        json!({ "type": "integer", "minimum": 0 }),
    );
    props.insert(
        "stratum".to_string(),
        json!({ "type": "integer", "minimum": 0 }),
    );
    props.insert(
        "tags".to_string(),
        json!({ "type": "array", "items": { "type": "string" } }),
    );
    props.insert(
        "selector".to_string(),
        json!({ "$ref": "#/$defs/selector" }),
    );
    props.insert("payload".to_string(), json!({ "type": "object" }));

    let mut required = Vec::new();
    if is_offer {
        for (fname, fschema) in &ps.payload {
            props.insert(fname.clone(), field_schema_to_json(fschema));
            if fschema.required {
                required.push(Value::String(fname.clone()));
            }
        }
    }

    let mut obj_schema = Map::new();
    obj_schema.insert("type".to_string(), Value::String("object".to_string()));
    obj_schema.insert("properties".to_string(), Value::Object(props));
    if !required.is_empty() {
        obj_schema.insert("required".to_string(), Value::Array(required));
    }

    let mut variants = vec![Value::Object(obj_schema)];
    if !is_offer || ps.payload.values().all(|f| !f.required) {
        variants.push(json!({ "const": true }));
    }
    if ps.cardinality == Cardinality::Budgeted {
        variants.push(json!({ "type": "integer", "minimum": 0 }));
    }

    let mut entry = Map::new();
    if !ps.description.is_empty() {
        entry.insert(
            "description".to_string(),
            Value::String(ps.description.clone()),
        );
    }
    entry.insert("oneOf".to_string(), Value::Array(variants));
    Value::Object(entry)
}

fn build_shorthand_table_schema(schemas: &SchemaCatalog, is_offer: bool) -> Value {
    let mut props = Map::new();
    for (ptype, ps) in &schemas.promises {
        let entry = promise_entry_json_schema(ps, is_offer);
        if ps.keyed {
            props.insert(
                ptype.clone(),
                json!({
                    "type": "object",
                    "description": ps.description,
                    "additionalProperties": entry,
                }),
            );
        } else {
            props.insert(ptype.clone(), entry);
        }
    }
    json!({
        "type": "object",
        "properties": Value::Object(props),
        "additionalProperties": !schemas.strict,
    })
}

/// Generates a standard JSON Schema (Draft 2020-12) document for `kind`, dynamically
/// specialized to all promise types declared in `schemas`.
#[must_use]
pub fn generate_json_schema(kind: SchemaKind, schemas: &SchemaCatalog) -> Value {
    match kind {
        SchemaKind::Agent => {
            let offer_schema = build_shorthand_table_schema(schemas, true);
            let use_schema = build_shorthand_table_schema(schemas, false);
            json!({
                "$schema": "https://json-schema.org/draft/2020-12/schema",
                "title": "Baugr Agent Manifest (agent.toml)",
                "type": "object",
                "required": ["id"],
                "additionalProperties": false,
                "properties": {
                    "id": { "type": "string", "minLength": 1 },
                    "description": { "type": "string" },
                    "attributes": { "type": "array", "items": { "type": "string" } },
                    "profiles": { "type": "array", "items": { "type": "string" } },
                    "contains": {
                        "type": "array",
                        "items": {
                            "oneOf": [
                                { "type": "string", "minLength": 1 },
                                {
                                    "type": "object",
                                    "required": ["agent"],
                                    "additionalProperties": false,
                                    "properties": {
                                        "agent": { "type": "string", "minLength": 1 },
                                        "instance": { "type": "string", "minLength": 1 },
                                        "promises": { "type": "array", "items": { "$ref": "#/$defs/rawPromise" } },
                                        "offer": offer_schema,
                                        "use": use_schema
                                    }
                                }
                            ]
                        }
                    },
                    "promises": { "type": "array", "items": { "$ref": "#/$defs/rawPromise" } },
                    "internal_promises": { "type": "array", "items": { "$ref": "#/$defs/rawPromise" } },
                    "offer": offer_schema,
                    "use": use_schema,
                    "internal": {
                        "type": "object",
                        "additionalProperties": false,
                        "properties": {
                            "offer": offer_schema,
                            "use": use_schema
                        }
                    }
                },
                "$defs": {
                    "selector": {
                        "oneOf": [
                            { "type": "string" },
                            {
                                "type": "object",
                                "required": ["kind"],
                                "properties": {
                                    "kind": { "type": "string", "enum": ["any", "none", "atom", "compl", "inter", "union", "diff"] },
                                    "tag": { "type": "string" },
                                    "inner": { "$ref": "#/$defs/selector" },
                                    "left": { "$ref": "#/$defs/selector" },
                                    "right": { "$ref": "#/$defs/selector" }
                                }
                            }
                        ]
                    },
                    "rawPromise": {
                        "type": "object",
                        "required": ["ptype", "polarity"],
                        "additionalProperties": false,
                        "properties": {
                            "ptype": { "type": "string", "minLength": 1 },
                            "key": { "type": "string" },
                            "polarity": { "type": "string", "enum": ["offer", "use"] },
                            "strength": { "type": "string", "enum": ["hard", "soft"] },
                            "cardinality": { "type": "string", "enum": ["exclusive", "broadcast", "partitioned", "budgeted"] },
                            "mandatory": { "type": "boolean" },
                            "amount": { "type": "integer", "minimum": 0 },
                            "priority": { "type": "integer", "minimum": 0 },
                            "stratum": { "type": "integer", "minimum": 0 },
                            "tags": { "type": "array", "items": { "type": "string" } },
                            "selector": { "$ref": "#/$defs/selector" },
                            "soft": { "type": "object" },
                            "default": {},
                            "payload": { "type": "object" }
                        }
                    }
                }
            })
        }
        SchemaKind::Profile => json!({
            "$schema": "https://json-schema.org/draft/2020-12/schema",
            "title": "Baugr Transparent Profile (profiles/*.toml)",
            "type": "object",
            "required": ["id"],
            "additionalProperties": false,
            "properties": {
                "id": { "type": "string", "minLength": 1 },
                "description": { "type": "string" },
                "profiles": { "type": "array", "items": { "type": "string" } },
                "agents": { "type": "array", "items": { "type": "string" } }
            }
        }),
        SchemaKind::Policy => json!({
            "$schema": "https://json-schema.org/draft/2020-12/schema",
            "title": "Baugr Policy & Invariant Catalog (policies/*.toml)",
            "type": "object",
            "additionalProperties": false,
            "properties": {
                "principals": { "type": "array", "items": { "type": "object" } },
                "resources": { "type": "array", "items": { "type": "object" } },
                "policies": { "type": "array", "items": { "type": "object" } },
                "auth_bindings": { "type": "array", "items": { "type": "object" } },
                "invariants": { "type": "array", "items": { "type": "object" } }
            }
        }),
        SchemaKind::Schema => json!({
            "$schema": "https://json-schema.org/draft/2020-12/schema",
            "title": "Baugr Promise Type Schema Registry (schemas/*.toml)",
            "type": "object",
            "additionalProperties": false,
            "properties": {
                "strict": { "type": "boolean" },
                "promises": {
                    "type": "object",
                    "additionalProperties": {
                        "type": "object",
                        "additionalProperties": false,
                        "properties": {
                            "description": { "type": "string" },
                            "cardinality": { "type": "string", "enum": ["exclusive", "broadcast", "partitioned", "budgeted"] },
                            "keyed": { "type": "boolean" },
                            "default_offer_mandatory": { "type": "boolean" },
                            "default_use_mandatory": { "type": "boolean" },
                            "default_strength": { "type": "string", "enum": ["hard", "soft"] },
                            "default_priority": { "type": "integer", "minimum": 0 },
                            "default_stratum": { "type": "integer", "minimum": 0 },
                            "default_tags": { "type": "array", "items": { "type": "string" } },
                            "key_from_payload": { "type": "string" },
                            "payload": {
                                "type": "object",
                                "additionalProperties": {
                                    "type": "object",
                                    "additionalProperties": false,
                                    "properties": {
                                        "type": { "type": "string", "enum": ["string", "integer", "number", "boolean", "array", "object", "any"] },
                                        "required": { "type": "boolean" },
                                        "description": { "type": "string" }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_schemas() -> SchemaCatalog {
        let mut promises = BTreeMap::new();
        promises.insert(
            "power:kw".to_string(),
            PromiseSchema {
                description: "Electric power capacity in kW".to_string(),
                cardinality: Cardinality::Budgeted,
                keyed: false,
                ..PromiseSchema::default()
            },
        );
        let mut feed_payload = BTreeMap::new();
        feed_payload.insert(
            "port".to_string(),
            FieldSchema {
                field_type: FieldType::Integer,
                required: true,
                description: "Endpoint port".to_string(),
            },
        );
        promises.insert(
            "signal:feed".to_string(),
            PromiseSchema {
                description: "Telemetry signal stream".to_string(),
                cardinality: Cardinality::Broadcast,
                keyed: true,
                default_tags: vec!["telemetry".to_string()],
                payload: feed_payload,
                ..PromiseSchema::default()
            },
        );
        SchemaCatalog {
            strict: true,
            promises,
        }
    }

    #[test]
    fn desugars_erg_l2_shorthand_to_exact_layer0() {
        let schemas = sample_schemas();
        let raw: RawAgentManifest = serde_json::from_value(json!({
            "id": "sensor-a",
            "contains": ["sub-child"],
            "offer": {
                "signal:feed": {
                    "voltage": {
                        "tags": ["high-freq"],
                        "port": 9100
                    }
                }
            },
            "use": {
                "power:kw": 12
            },
            "internal": {
                "offer": {
                    "power:kw": { "amount": 50 }
                }
            }
        }))
        .unwrap();

        let manifest = desugar_agent(raw, &schemas).unwrap();
        assert_eq!(manifest.contains.len(), 1);
        assert_eq!(manifest.contains[0].agent, "sub-child");
        assert_eq!(manifest.promises.len(), 2);

        let feed = &manifest.promises[0];
        assert_eq!(feed.ptype, "signal:feed");
        assert_eq!(feed.key, "voltage");
        assert_eq!(feed.polarity, Polarity::Offer);
        assert_eq!(feed.cardinality, Cardinality::Broadcast);
        assert_eq!(feed.tags, vec!["telemetry", "high-freq"]);
        assert_eq!(feed.payload.get("port"), Some(&json!(9100)));

        let pwr = &manifest.promises[1];
        assert_eq!(pwr.ptype, "power:kw");
        assert_eq!(pwr.key, "power:kw");
        assert_eq!(pwr.polarity, Polarity::Use);
        assert_eq!(pwr.cardinality, Cardinality::Budgeted);
        assert_eq!(pwr.amount, 12);

        assert_eq!(manifest.internal_promises.len(), 1);
        assert_eq!(manifest.internal_promises[0].amount, 50);
    }

    #[test]
    fn validates_strict_unknown_ptype_and_payload_types() {
        let schemas = sample_schemas();
        let mut fleet = FleetSpec {
            schemas: schemas.clone(),
            ..FleetSpec::default()
        };
        let raw: RawAgentManifest = serde_json::from_value(json!({
            "id": "bad-sensor",
            "offer": {
                "signal:feed": {
                    "missing": {},
                    "wrong-type": { "port": "not-an-int" }
                },
                "typo:unknown": true
            }
        }))
        .unwrap();
        let manifest = desugar_agent(raw, &schemas).unwrap();
        fleet.agents.insert(manifest.id.clone(), manifest);

        let errs = validate_fleet_schemas(&fleet, &schemas);
        assert!(errs.iter().any(|e| matches!(
            e,
            SchemaError::MissingRequiredField { field, .. } if field == "port"
        )));
        assert!(errs.iter().any(|e| matches!(
            e,
            SchemaError::InvalidFieldType { field, expected: FieldType::Integer, .. } if field == "port"
        )));
        assert!(errs.iter().any(|e| matches!(
            e,
            SchemaError::UnknownPromiseType { ptype, .. } if ptype == "typo:unknown"
        )));
    }
}
