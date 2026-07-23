// Example/dev tool: dumps rule variants to stdout by design; allow the
// `disallowed_macros` convention freeze for this example binary.
#![allow(clippy::disallowed_macros)]

mod common;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: dump_variants <theory> <rule_name>");
        std::process::exit(2);
    }
    let theory_path = &args[1];
    let rule_name = &args[2];
    let (_parsed, elaborated, maude) = common::load_theory_with_maude(theory_path);
    for open in elaborated.rules() {
        let r = &open.rule;
        let n = match &r.info.name {
            tamarin_theory::rule::ProtoRuleName::Stand(s) => *s,
            _ => "",
        };
        if n == *rule_name {
            println!("rule {}: pre", n);
            for f in &r.premises {
                println!("  prem: {:?}", f);
            }
            for f in &r.conclusions {
                println!("  conc: {:?}", f);
            }
            for f in &r.actions {
                println!("  act:  {:?}", f);
            }
            // Compute variants
            let substs = tamarin_theory::tools::rule_variants::variant_substs_for_rule(&maude, r)
                .expect("variants");
            println!("variants ({}):", substs.len());
            for (i, s) in substs.iter().enumerate() {
                println!("  [{}] {:?}", i, s);
            }
            return;
        }
    }
    eprintln!("rule not found: {}", rule_name);
}
