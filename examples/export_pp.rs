use ibc::params::{LABEL_DERIVED, LABEL_G_IDEN, LABEL_G_RAN, LABEL_G_VAL, PublicParams};

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

fn main() {
    let pp = PublicParams::setup();
    let [iden, val, ran] = pp.to_bytes();

    println!("{{");
    println!("  \"group\": \"ristretto255\",");
    println!("  \"hash_to_group\": \"RistrettoPoint::hash_from_bytes::<Sha512>(label)\",");
    println!("  \"generators\": [");
    println!("    {{ \"name\": \"g_iden\", \"label\": \"{}\", \"bytes\": \"{}\" }},", text(LABEL_G_IDEN), hex(&iden));
    println!("    {{ \"name\": \"g_val\",  \"label\": \"{}\", \"bytes\": \"{}\" }},", text(LABEL_G_VAL), hex(&val));
    println!("    {{ \"name\": \"g_ran\",  \"label\": \"{}\", \"bytes\": \"{}\" }}", text(LABEL_G_RAN), hex(&ran));
    println!("  ],");
    println!("  \"aliases\": {{ \"g\": \"g_val\", \"h\": \"g_ran\" }},");
    println!("  \"derived_label\": \"{}<set>/<i as u32 little-endian>\",", text(LABEL_DERIVED));

    let sets: Vec<(String, usize)> = std::env::args()
        .skip(1)
        .map(|arg| {
            let (set, n) = arg.split_once('=').expect("argument must be set=n");
            (set.to_string(), n.parse().expect("n must be a number"))
        })
        .collect();
    println!("  \"derived\": [");
    for (k, (set, n)) in sets.iter().enumerate() {
        let gens: Vec<String> = pp
            .derive_generators(set.as_bytes(), *n)
            .iter()
            .map(|g| format!("\"{}\"", hex(g.compress().as_bytes())))
            .collect();
        let comma = if k + 1 < sets.len() { "," } else { "" };
        println!("    {{ \"set\": \"{set}\", \"bytes\": [{}] }}{comma}", gens.join(", "));
    }
    println!("  ]");
    println!("}}");
}
