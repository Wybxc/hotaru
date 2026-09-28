use hotaru_sys::{Name, Source, SourceKind, Term, TermKind, Theorem, Theory, Type};
use std::{collections::HashMap, env, fs, hint::black_box, time::Instant};

const FIXTURE: &[u8] = include_bytes!("../../benchmarks/list_not_nil/list_not_nil.art");
const AXIOM_COUNT: usize = 31;

type RunResult<T> = std::result::Result<T, String>;

fn native<T>(result: hotaru_sys::Result<T>) -> RunResult<T> {
    result.map_err(|error| format!("{error:?}"))
}

fn invalid<T>(message: &str) -> RunResult<T> {
    Err(message.to_owned())
}

fn setting(name: &str) -> usize {
    let value: usize = env::var(name)
        .unwrap_or_else(|_| panic!("{name} is required"))
        .parse()
        .unwrap_or_else(|_| panic!("invalid {name}"));
    assert!(value > 0, "{name} must be positive");
    value
}

fn qname(scope: &str, name: &str) -> Name {
    Name::new(scope, name)
}

fn function(args: &[&Type], result: &Type) -> RunResult<Type> {
    args.iter()
        .rev()
        .try_fold(result.clone(), |out, arg| native(Type::function(arg, &out)))
}

fn list_type(element: &Type) -> RunResult<Type> {
    native(Type::operator(&qname("HOL4.list", "list"), &[element]))
}

fn bool_lambda(connective: &str, ty: &Type) -> RunResult<Term> {
    let domain = native(ty.child(0))?;
    let outer = native(Term::bound(1))?;
    let inner = native(Term::bound(0))?;
    let body = match connective {
        "=" => native(Term::equal(&outer, &inner))?,
        "==>" => native(Term::imp(&outer, &inner))?,
        _ => return invalid("unknown connective lambda"),
    };
    let inner = native(Term::lambda(&domain, &body))?;
    native(Term::lambda(&domain, &inner))
}

fn declare_signature() -> RunResult<Theory> {
    let mut theory = native(Theory::new())?;
    theory = native(theory.with_source(&Source::new(
        SourceKind::Checkpoint,
        "benchmarks/list_not_nil/list_not_nil.art",
    )))?;
    let boolean = native(Type::bool())?;
    let element = native(Type::var("A"))?;
    let list = list_type(&element)?;
    let predicate = function(&[&element], &boolean)?;

    theory = native(theory.declare_type(&qname("HOL4.list", "list"), 1))?;
    for (name, ty) in [
        ("!", function(&[&predicate], &boolean)?),
        ("?", function(&[&predicate], &boolean)?),
        ("T", boolean.clone()),
        ("F", boolean.clone()),
        ("/\\", function(&[&boolean, &boolean], &boolean)?),
        ("\\/", function(&[&boolean, &boolean], &boolean)?),
        ("~", function(&[&boolean], &boolean)?),
    ] {
        theory = native(theory.declare_const(&qname("HOL4.bool", name), &ty))?;
    }
    for (name, ty) in [
        ("NIL", list.clone()),
        ("CONS", function(&[&element, &list], &list)?),
        ("HD", function(&[&list], &element)?),
        ("TL", function(&[&list], &list)?),
    ] {
        theory = native(theory.declare_const(&qname("HOL4.list", name), &ty))?;
    }
    Ok(theory)
}

fn const_term(name: &str, ty: &Type) -> RunResult<Term> {
    match name {
        "=" | "HOL4.min.=" => bool_lambda("=", ty),
        "HOL4.min.==>" => bool_lambda("==>", ty),
        "HOL4.min.@" => {
            let selected = native(ty.child(1))?;
            native(Term::constant(&qname("min", "@"), &[("a", &selected)]))
        }
        "HOL4.bool.!" | "HOL4.bool.?" => {
            let element = native(native(ty.child(0))?.child(0))?;
            native(Term::constant(
                &qname("HOL4.bool", &name[10..]),
                &[("A", &element)],
            ))
        }
        "HOL4.bool.T" | "HOL4.bool.F" | "HOL4.bool.~" | "HOL4.bool./\\" | "HOL4.bool.\\/" => {
            native(Term::constant(&qname("HOL4.bool", &name[10..]), &[]))
        }
        "HOL4.list.NIL" | "HOL4.list.CONS" | "HOL4.list.HD" | "HOL4.list.TL" => {
            let element = match name {
                "HOL4.list.NIL" => native(ty.child(0))?,
                "HOL4.list.CONS" => native(ty.child(0))?,
                _ => native(native(ty.child(0))?.child(0))?,
            };
            native(Term::constant(
                &qname("HOL4.list", &name[10..]),
                &[("A", &element)],
            ))
        }
        _ => invalid(&format!("unmapped certificate constant: {name}")),
    }
}

fn close(name: &str, ty: &Type, term: &Term, depth: u64) -> RunResult<Term> {
    match term.kind() {
        TermKind::Free => {
            if term.name().map_err(|error| format!("{error:?}"))? == name
                && native(term.annotation())? == *ty
            {
                native(Term::bound(depth))
            } else {
                Ok(term.clone())
            }
        }
        TermKind::Bound | TermKind::Constant => Ok(term.clone()),
        TermKind::Application => native(Term::app(
            &close(name, ty, &native(term.child(0))?, depth)?,
            &close(name, ty, &native(term.child(1))?, depth)?,
        )),
        TermKind::Lambda => native(Term::lambda(
            &native(term.annotation())?,
            &close(name, ty, &native(term.child(0))?, depth + 1)?,
        )),
        TermKind::Equality => native(Term::equal(
            &close(name, ty, &native(term.child(0))?, depth)?,
            &close(name, ty, &native(term.child(1))?, depth)?,
        )),
        TermKind::Implication => native(Term::imp(
            &close(name, ty, &native(term.child(0))?, depth)?,
            &close(name, ty, &native(term.child(1))?, depth)?,
        )),
    }
}

fn describe(term: &Term) -> RunResult<String> {
    match term.kind() {
        TermKind::Free => Ok(format!("{}", native(term.name())?)),
        TermKind::Bound => Ok(format!("#{}", native(term.bound_index())?)),
        TermKind::Constant => Ok(format!(
            "{}.{}",
            native(term.scope())?,
            native(term.name())?
        )),
        TermKind::Application => Ok(format!(
            "({} {})",
            describe(&native(term.child(0))?)?,
            describe(&native(term.child(1))?)?
        )),
        TermKind::Lambda => Ok(format!("(lam {})", describe(&native(term.child(0))?)?)),
        TermKind::Equality => Ok(format!(
            "({} = {})",
            describe(&native(term.child(0))?)?,
            describe(&native(term.child(1))?)?
        )),
        TermKind::Implication => Ok(format!(
            "({} ==> {})",
            describe(&native(term.child(0))?)?,
            describe(&native(term.child(1))?)?
        )),
    }
}

#[derive(Clone)]
struct Proof {
    theorem: Theorem,
    assumptions: u64,
}

impl Proof {
    fn raw(theorem: Theorem, assumptions: u64) -> Self {
        Self {
            theorem,
            assumptions,
        }
    }

    fn assumptions(&self) -> u64 {
        self.assumptions
    }

    fn compact(
        &mut self,
        theory: &Theory,
        compact_threshold: u64,
        compact_calls: &mut usize,
    ) -> RunResult<()> {
        if self.assumptions > compact_threshold {
            *compact_calls += 1;
            self.theorem = native(theory.contract(&self.theorem))?;
            self.assumptions = self.theorem.assumption_count();
        }
        Ok(())
    }

    fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}

#[derive(Clone)]
enum Value {
    Name(String),
    Number(usize),
    TypeOp(String),
    Ty(Type),
    Constant(String),
    Var { name: String, ty: Type, term: Term },
    Term(Term),
    Proof(Option<Proof>),
    Values(Vec<Value>),
}

struct Machine<'a> {
    theory: &'a Theory,
    imported: &'a [Theorem],
    scan: bool,
    stack: Vec<Value>,
    dictionary: HashMap<usize, Value>,
    axioms: Vec<Term>,
    outputs: Vec<Proof>,
    conversion_boundaries: usize,
    compact_calls: usize,
    compact_threshold: u64,
}

impl<'a> Machine<'a> {
    fn new(theory: &'a Theory, imported: &'a [Theorem], scan: bool) -> Self {
        Self {
            theory,
            imported,
            scan,
            stack: Vec::new(),
            dictionary: HashMap::new(),
            axioms: Vec::new(),
            outputs: Vec::new(),
            conversion_boundaries: 0,
            compact_calls: 0,
            compact_threshold: env::var("LIST_NOT_NIL_COMPACT_THRESHOLD")
                .ok()
                .and_then(|value| value.parse().ok())
                .unwrap_or(2),
        }
    }

    fn pop(&mut self) -> RunResult<Value> {
        self.stack
            .pop()
            .ok_or_else(|| "article stack underflow".to_owned())
    }

    fn name(&mut self) -> RunResult<String> {
        match self.pop()? {
            Value::Name(name) => Ok(name),
            _ => invalid("expected article name"),
        }
    }

    fn number(&mut self) -> RunResult<usize> {
        match self.pop()? {
            Value::Number(number) => Ok(number),
            _ => invalid("expected article number"),
        }
    }

    fn ty(&mut self) -> RunResult<Type> {
        match self.pop()? {
            Value::Ty(ty) => Ok(ty),
            _ => invalid("expected article type"),
        }
    }

    fn term(&mut self) -> RunResult<Term> {
        match self.pop()? {
            Value::Term(term) => Ok(term),
            _ => invalid("expected article term"),
        }
    }

    fn var(&mut self) -> RunResult<(String, Type, Term)> {
        match self.pop()? {
            Value::Var { name, ty, term } => Ok((name, ty, term)),
            _ => invalid("expected article variable"),
        }
    }

    fn values(&mut self) -> RunResult<Vec<Value>> {
        match self.pop()? {
            Value::Values(values) => Ok(values),
            _ => invalid("expected article list"),
        }
    }

    fn proof(&mut self) -> RunResult<Option<Proof>> {
        match self.pop()? {
            Value::Proof(proof) => Ok(proof),
            _ => invalid("expected article theorem"),
        }
    }

    fn terms(values: Vec<Value>) -> RunResult<Vec<Term>> {
        values
            .into_iter()
            .map(|value| match value {
                Value::Term(term) => Ok(term),
                _ => invalid("expected term in article list"),
            })
            .collect()
    }

    fn types(values: Vec<Value>) -> RunResult<Vec<Type>> {
        values
            .into_iter()
            .map(|value| match value {
                Value::Ty(ty) => Ok(ty),
                _ => invalid("expected type in article list"),
            })
            .collect()
    }

    fn prove(&mut self, value: Option<Proof>) -> RunResult<()> {
        if let Some(mut proof) = value {
            proof.compact(self.theory, self.compact_threshold, &mut self.compact_calls)?;
            self.stack.push(Value::Proof(Some(proof)));
        } else {
            self.stack.push(Value::Proof(None));
        }
        Ok(())
    }

    fn prove_compacted(&mut self, value: Option<Proof>) -> RunResult<()> {
        self.stack.push(Value::Proof(value));
        Ok(())
    }

    fn execute(&mut self, command: &str) -> RunResult<()> {
        match command {
            "version" => {
                if self.number()? != 6 {
                    return invalid("unsupported OpenTheory version");
                }
            }
            "nil" => self.stack.push(Value::Values(Vec::new())),
            "cons" => {
                let mut tail = self.values()?;
                tail.insert(0, self.pop()?);
                self.stack.push(Value::Values(tail));
            }
            "def" => {
                let key = self.number()?;
                let value = self.pop()?;
                if self.dictionary.insert(key, value.clone()).is_some() {
                    return invalid("duplicate article dictionary key");
                }
                self.stack.push(value);
            }
            "ref" => {
                let key = self.number()?;
                self.stack.push(
                    self.dictionary
                        .get(&key)
                        .ok_or_else(|| "unknown article dictionary key".to_owned())?
                        .clone(),
                );
            }
            "remove" => {
                let key = self.number()?;
                self.stack.push(
                    self.dictionary
                        .remove(&key)
                        .ok_or_else(|| "unknown article dictionary key".to_owned())?,
                );
            }
            "pop" => {
                self.pop()?;
            }
            "typeOp" => {
                let name = self.name()?;
                self.stack.push(Value::TypeOp(name));
            }
            "varType" => {
                let name = self.name()?;
                self.stack.push(Value::Ty(native(Type::var(&name))?));
            }
            "opType" => {
                let args = Self::types(self.values()?)?;
                let op = match self.pop()? {
                    Value::TypeOp(name) => name,
                    _ => return invalid("expected article type operator"),
                };
                let ty = match op.as_str() {
                    "bool" => {
                        if !args.is_empty() {
                            return invalid("bool type has arguments");
                        }
                        native(Type::bool())?
                    }
                    "->" => {
                        if args.len() != 2 {
                            return invalid("function type requires two arguments");
                        }
                        native(Type::function(&args[0], &args[1]))?
                    }
                    "HOL4.list.list" => {
                        if args.len() != 1 {
                            return invalid("list type requires one argument");
                        }
                        list_type(&args[0])?
                    }
                    _ => return invalid("unmapped article type operator"),
                };
                self.stack.push(Value::Ty(ty));
            }
            "const" => {
                let name = self.name()?;
                self.stack.push(Value::Constant(name));
            }
            "constTerm" => {
                let ty = self.ty()?;
                let name = match self.pop()? {
                    Value::Constant(name) => name,
                    _ => return invalid("expected article constant"),
                };
                self.stack.push(Value::Term(const_term(&name, &ty)?));
            }
            "var" => {
                let ty = self.ty()?;
                let name = self.name()?;
                let term = native(Term::free(&name, &ty))?;
                self.stack.push(Value::Var { name, ty, term });
            }
            "varTerm" => {
                let (_, _, term) = self.var()?;
                self.stack.push(Value::Term(term));
            }
            "absTerm" => {
                let body = self.term()?;
                let (name, ty, _) = self.var()?;
                self.stack.push(Value::Term(native(Term::lambda(
                    &ty,
                    &close(&name, &ty, &body, 0)?,
                ))?));
            }
            "appTerm" => {
                let arg = self.term()?;
                let fun = self.term()?;
                self.stack.push(Value::Term(native(Term::app(&fun, &arg))?));
            }
            "axiom" => {
                let conclusion = self.term()?;
                if !Self::terms(self.values()?)?.is_empty() {
                    return invalid("article axiom has hypotheses");
                }
                let index = self.axioms.len();
                self.axioms.push(conclusion.clone());
                if self.scan {
                    self.prove(None)?;
                } else {
                    let theorem = self
                        .imported
                        .get(index)
                        .ok_or_else(|| "unapproved article axiom".to_owned())?;
                    if theorem.conclusion() != conclusion || theorem.assumption_count() != 0 {
                        return invalid("article axiom differs from approved fixture");
                    }
                    self.prove(Some(Proof::raw(theorem.clone(), 0)))?;
                }
            }
            "assume" => {
                let term = self.term()?;
                let proof = if self.scan {
                    None
                } else {
                    Some(Proof::raw(native(self.theory.assume(&term))?, 1))
                };
                self.prove(proof)?;
            }
            "refl" | "betaConv" => {
                let term = self.term()?;
                let proof = if self.scan {
                    None
                } else {
                    let theorem = if command == "refl" {
                        native(self.theory.refl(&term))?
                    } else {
                        native(self.theory.beta(&term))?
                    };
                    Some(Proof::raw(theorem, 0))
                };
                self.prove(proof)?;
            }
            "absThm" => {
                let theorem = self.proof()?;
                let (name, ty, _) = self.var()?;
                let proof = if let Some(theorem) = theorem {
                    let result = native(self.theory.abs(&name, &ty, theorem.theorem()))?;
                    Some(Proof::raw(result, theorem.assumptions()))
                } else {
                    None
                };
                self.prove(proof)?;
            }
            "appThm" | "deductAntisym" | "trans" => {
                let second = self.proof()?;
                let first = self.proof()?;
                let mut compacted = false;
                let proof = if let (Some(first), Some(second)) = (&first, &second) {
                    let native_eq = match command {
                        "appThm" => native(self.theory.mk_comb(first.theorem(), second.theorem()))?,
                        "deductAntisym" => {
                            compacted = true;
                            native(
                                self.theory
                                    .deduct_antisym(first.theorem(), second.theorem()),
                            )?
                        }
                        _ => native(self.theory.trans(first.theorem(), second.theorem()))?,
                    };
                    let assumptions = if command == "deductAntisym" {
                        // This rule removes assumptions equivalent to either conclusion;
                        // keep the kernel's exact count before applying the normal cache.
                        native_eq.assumption_count()
                    } else {
                        first.assumptions() + second.assumptions()
                    };
                    Some(Proof::raw(native_eq, assumptions))
                } else {
                    None
                };
                if compacted {
                    self.prove_compacted(proof)?;
                } else {
                    self.prove(proof)?;
                }
            }
            "sym" => {
                let theorem = self.proof()?;
                let proof = if let Some(theorem) = &theorem {
                    let result = native(self.theory.symm(theorem.theorem()))?;
                    Some(Proof::raw(result, theorem.assumptions()))
                } else {
                    None
                };
                self.prove(proof)?;
            }
            "eqMp" => {
                let premise = self.proof()?;
                let equality = self.proof()?;
                let proof = if let (Some(premise), Some(equality)) = (premise, equality) {
                    let equality_assumptions = equality.assumptions();
                    let premise_assumptions = premise.assumptions();
                    let result = self
                        .theory
                        .eq_mp(equality.theorem(), premise.theorem())
                        .map_err(|error| {
                            let expected = equality.theorem().conclusion().child(0).ok();
                            format!(
                                "{error:?}: equality-left={}, premise={}",
                                expected
                                    .as_ref()
                                    .and_then(|term| describe(term).ok())
                                    .unwrap_or_default(),
                                describe(&premise.theorem().conclusion()).unwrap_or_default()
                            )
                        })?;
                    let assumptions = if equality_assumptions == 0 {
                        premise_assumptions
                    } else if premise_assumptions == 0 {
                        equality_assumptions
                    } else {
                        result.assumption_count()
                    };
                    Some(Proof::raw(result, assumptions))
                } else {
                    None
                };
                self.prove_compacted(proof)?;
            }
            "subst" => {
                let proof = self.proof()?;
                let substitutions = self.values()?;
                let [Value::Values(type_pairs), Value::Values(term_pairs)] =
                    <[Value; 2]>::try_from(substitutions)
                        .map_err(|_| "invalid substitution lists".to_owned())?
                else {
                    return invalid("invalid substitution lists");
                };
                let ty_subst = type_pairs
                    .into_iter()
                    .map(|pair| match pair {
                        Value::Values(items) => match <[Value; 2]>::try_from(items) {
                            Ok([Value::Name(name), Value::Ty(ty)]) => Ok((name, ty)),
                            _ => invalid("invalid type substitution pair"),
                        },
                        _ => invalid("invalid type substitution pair"),
                    })
                    .collect::<RunResult<Vec<_>>>()?;
                let tm_subst = term_pairs
                    .into_iter()
                    .map(|pair| match pair {
                        Value::Values(items) => match <[Value; 2]>::try_from(items) {
                            Ok([Value::Var { term, .. }, Value::Term(replacement)]) => {
                                Ok((term, replacement))
                            }
                            _ => invalid("invalid term substitution pair"),
                        },
                        _ => invalid("invalid term substitution pair"),
                    })
                    .collect::<RunResult<Vec<_>>>()?;
                let proof = if let Some(proof) = proof {
                    let mut theorem = proof.theorem().clone();
                    let type_pairs = ty_subst
                        .iter()
                        .map(|(name, ty)| (name.as_str(), ty))
                        .collect::<Vec<_>>();
                    let term_pairs = tm_subst
                        .iter()
                        .map(|(var, term)| (var, term))
                        .collect::<Vec<_>>();
                    if !type_pairs.is_empty() && !term_pairs.is_empty() {
                        theorem =
                            native(self.theory.inst_ty_term(&type_pairs, &term_pairs, &theorem))?;
                    } else if !type_pairs.is_empty() {
                        theorem = native(self.theory.inst_type(&type_pairs, &theorem))?;
                    } else if !term_pairs.is_empty() {
                        theorem = native(self.theory.inst(&term_pairs, &theorem))?;
                    }
                    Some(Proof::raw(theorem, proof.assumptions()))
                } else {
                    None
                };
                self.prove(proof)?;
            }
            "thm" => {
                let conclusion = self.term()?;
                let hypotheses = Self::terms(self.values()?)?;
                let theorem = self.proof()?;
                if !hypotheses.is_empty() {
                    return invalid("LIST_NOT_NIL export has assumptions");
                }
                if let Some(proof) = theorem {
                    if proof.theorem().conclusion() != conclusion || proof.assumptions() != 0 {
                        return invalid("exported theorem differs from article statement");
                    }
                    self.outputs.push(proof);
                }
            }
            "defineConst" | "defineTypeOp" => {
                return invalid("certificate attempted an unsupported definition");
            }
            _ => return invalid(&format!("unsupported article command: {command}")),
        }
        Ok(())
    }
}

fn decode_name(line: &str) -> RunResult<String> {
    let quoted = line
        .strip_prefix('"')
        .and_then(|line| line.strip_suffix('"'))
        .ok_or_else(|| "invalid article name".to_owned())?;
    let mut chars = quoted.chars();
    let mut decoded = String::new();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            decoded.push(
                chars
                    .next()
                    .ok_or_else(|| "invalid name escape".to_owned())?,
            );
        } else {
            decoded.push(ch);
        }
    }
    Ok(decoded)
}

fn run_article<'a>(path: &str, mut machine: Machine<'a>) -> RunResult<Machine<'a>> {
    let article = fs::read_to_string(path).map_err(|error| error.to_string())?;
    for (index, line) in article.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let result = if line.starts_with('"') {
            machine.stack.push(Value::Name(decode_name(line)?));
            Ok(())
        } else if line.bytes().all(|ch| ch.is_ascii_digit()) {
            machine.stack.push(Value::Number(
                line.parse()
                    .map_err(|_| "invalid article number".to_owned())?,
            ));
            Ok(())
        } else {
            machine.execute(line)
        };
        result.map_err(|error| format!("article line {} ({line}): {error}", index + 1))?;
    }
    if machine.axioms.len() != AXIOM_COUNT {
        return invalid("unexpected number of article axiom references");
    }
    if machine.scan {
        if !machine.outputs.is_empty() {
            return invalid("symbolic scan constructed a theorem");
        }
    } else if machine.outputs.len() != 1 {
        return invalid("article must export exactly one theorem");
    }
    Ok(machine)
}

fn setup(path: &str) -> RunResult<(Theory, Vec<Theorem>)> {
    let bytes = fs::read(path).map_err(|error| error.to_string())?;
    if bytes != FIXTURE {
        return invalid("article differs from the pinned LIST_NOT_NIL fixture");
    }
    let theory = declare_signature()?;
    let scan = run_article(path, Machine::new(&theory, &[], true))?;
    let mut final_theory = theory.clone();
    let mut axioms = Vec::with_capacity(AXIOM_COUNT);
    for proposition in &scan.axioms {
        let (next, theorem) = native(final_theory.add_axiom(proposition))?;
        final_theory = next;
        axioms.push(theorem);
    }
    let axioms = axioms
        .iter()
        .map(|theorem| native(theorem.rebase(&final_theory)))
        .collect::<RunResult<Vec<_>>>()?;
    Ok((final_theory, axioms))
}

fn applied_eq(left: &Term, right: &Term, ty: &Type) -> RunResult<Term> {
    let connective = bool_lambda("=", &function(&[ty, ty], &native(Type::bool())?)?)?;
    native(Term::app(&native(Term::app(&connective, left))?, right))
}

fn expected_conclusion(article_encoding: bool) -> RunResult<Term> {
    let element = native(Type::var("A"))?;
    let list = list_type(&element)?;
    let boolean = native(Type::bool())?;
    let ls = native(Term::free("ls", &list))?;
    let nil = native(Term::constant(
        &qname("HOL4.list", "NIL"),
        &[("A", &element)],
    ))?;
    let cons = native(Term::constant(
        &qname("HOL4.list", "CONS"),
        &[("A", &element)],
    ))?;
    let hd = native(Term::constant(
        &qname("HOL4.list", "HD"),
        &[("A", &element)],
    ))?;
    let tl = native(Term::constant(
        &qname("HOL4.list", "TL"),
        &[("A", &element)],
    ))?;
    let negation = native(Term::constant(&qname("HOL4.bool", "~"), &[]))?;
    let all = native(Term::constant(&qname("HOL4.bool", "!"), &[("A", &list)]))?;

    let make_eq = |left: &Term, right: &Term, ty: &Type| {
        if article_encoding {
            applied_eq(left, right, ty)
        } else {
            native(Term::equal(left, right))
        }
    };
    let nil_eq = make_eq(&ls, &nil, &list)?;
    let not_nil = native(Term::app(&negation, &nil_eq))?;
    let hd_ls = native(Term::app(&hd, &ls))?;
    let tl_ls = native(Term::app(&tl, &ls))?;
    let cons_ls = native(Term::app(&native(Term::app(&cons, &hd_ls))?, &tl_ls))?;
    let rebuilt_eq = make_eq(&ls, &cons_ls, &list)?;
    let body = make_eq(&not_nil, &rebuilt_eq, &boolean)?;
    let predicate = native(Term::lambda(&list, &close("ls", &list, &body, 0)?))?;
    native(Term::app(&all, &predicate))
}

fn verify(theory: &Theory, proof: &Proof) -> RunResult<()> {
    let theorem = proof.theorem();
    if proof.assumptions() != 0 {
        return invalid("LIST_NOT_NIL has assumptions");
    }
    let conclusion = theorem.conclusion();
    native(theory.check(&conclusion))?;
    if conclusion != expected_conclusion(true)? {
        return invalid(&format!(
            "LIST_NOT_NIL conclusion mismatch: {}",
            describe(&conclusion)?
        ));
    }
    Ok(())
}

fn sample(
    path: &str,
    theory: &Theory,
    axioms: &[Theorem],
    iterations: usize,
) -> RunResult<(u128, Proof, usize, usize)> {
    let start = Instant::now();
    let mut last = None;
    let mut conversion_boundaries = 0;
    let mut compact_calls = 0;
    for _ in 0..iterations {
        let mut replay = run_article(path, Machine::new(theory, axioms, false))?;
        conversion_boundaries += replay.conversion_boundaries;
        compact_calls += replay.compact_calls;
        let proof = replay
            .outputs
            .pop()
            .ok_or_else(|| "missing export".to_owned())?;
        last = Some(proof);
    }
    black_box(&last);
    let elapsed = start.elapsed().as_nanos();
    Ok((
        elapsed,
        last.ok_or_else(|| "empty sample".to_owned())?,
        conversion_boundaries,
        compact_calls,
    ))
}

fn main() {
    let path = env::args()
        .nth(1)
        .expect("usage: list_not_nil_replay ARTICLE");
    let iterations = setting("LIST_NOT_NIL_ITERATIONS");
    let trials = setting("LIST_NOT_NIL_TRIALS");
    let warmup = setting("LIST_NOT_NIL_WARMUP");
    let (theory, axioms) = setup(&path).unwrap_or_else(|error| panic!("setup: {error}"));
    let (_, warm, _, _) =
        sample(&path, &theory, &axioms, warmup).unwrap_or_else(|error| panic!("warmup: {error}"));
    verify(&theory, &warm).unwrap_or_else(|error| panic!("warmup check: {error}"));
    for trial in 0..trials {
        let (elapsed_ns, theorem, conversion_boundaries, compact_calls) =
            sample(&path, &theory, &axioms, iterations)
                .unwrap_or_else(|error| panic!("trial {trial}: {error}"));
        verify(&theory, &theorem).unwrap_or_else(|error| panic!("trial check: {error}"));
        eprintln!("LIST_NOT_NIL_CONVERSION_BOUNDARIES\t{trial}\t{conversion_boundaries}");
        eprintln!("LIST_NOT_NIL_COMPACT_CALLS\t{trial}\t{compact_calls}");
        println!("LIST_NOT_NIL_REPLAY\thotaru\t{trial}\t{iterations}\t{elapsed_ns}");
    }
}
