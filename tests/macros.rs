// Copyright the pasta-asm contributors.
// SPDX-License-Identifier: Apache-2.0

pasta_asm::if_supported! {
    fn backend_name() -> &'static str { pasta_asm::BACKEND }
}
pasta_asm::if_unsupported! {
    fn backend_name() -> &'static str { "portable" }
}

fn selected_backend() -> bool {
    pasta_asm::if_supported! {{ pasta_asm::BACKEND != "portable" }}
    pasta_asm::if_unsupported! {{ false }}
}

#[test]
fn cfg_gated_local_bindings_and_blocks() {
    pasta_asm::if_supported! { let backend: &str = backend_name(); }
    pasta_asm::if_unsupported! { let backend: &str = backend_name(); }
    pasta_asm::if_supported! {{ assert_ne!(backend, "portable"); }}
    pasta_asm::if_unsupported! {{ assert_eq!(backend, "portable"); }}
    assert_eq!(backend == "portable", !selected_backend());
}
