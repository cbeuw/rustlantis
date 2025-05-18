use difftest::backends;
use difftest::{Source, run_diff_test};

#[test]
fn correct_mir() {
    let config = config::load("tests/config.toml");
    let backends = backends::from_config(config);

    let results = run_diff_test(&Source::File("tests/inputs/simple.rs".into()), backends);
    println!("{}", results);
    assert!(results.all_same());
    assert!(
        results["llvm"]
            .as_ref()
            .is_ok_and(|output| output.status.success() && output.stdout == "5\n")
    )
}

#[test]
fn invalid_mir() {
    let config = config::load("tests/config.toml");
    let backends = backends::from_config(config);

    let results = run_diff_test(
        &Source::File("tests/inputs/invalid_mir.rs".into()),
        backends,
    );
    println!("{}", results);
    assert!(results.all_same());
    assert!(results["miri"].is_err());
    assert_eq!(results.has_ub(), Some(false));
}

#[test]
fn ub() {
    let config = config::load("tests/config.toml");
    let backends = backends::from_config(config);

    let results = run_diff_test(&Source::File("tests/inputs/ub.rs".into()), backends);
    println!("{}", results);
    assert_eq!(results.has_ub(), Some(true));
}
