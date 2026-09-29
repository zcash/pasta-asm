// Copyright the pasta-asm contributors.
// SPDX-License-Identifier: Apache-2.0

//! The inversion per call on 1000 random canonical inputs of the Pallas base field, and, where
//! the crate has a Montgomery backend, the multiplication and the squaring for scale. Built as
//! is, `invert` runs the backend's blocks where there are any; built with
//! `RUSTFLAGS='--cfg pasta_asm_disable'`, it runs the portable blocks on the same inputs.

use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use std::hint::black_box;

/// The Pallas base field's modulus, `inv`, and `v0 = 2^562 mod p`, as in the crate's tests.
const MODULUS: [u64; 4] = [
    0x992d30ed00000001,
    0x224698fc094cf91b,
    0x0000000000000000,
    0x4000000000000000,
];
const INV: u64 = 0x992d30ecffffffff;
const V0: [u64; 4] = [
    0x9a5f583ce5084635,
    0x4f417e233776c195,
    0x74634b1a733f7785,
    0x1c51de5ea66f0f25,
];

const INPUTS: usize = 1000;

/// `INPUTS` uniform values below `2^254`, so canonical, from a fixed xorshift seed.
fn inputs() -> Vec<[u64; 4]> {
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    (0..INPUTS)
        .map(|_| [next(), next(), next(), next() >> 2])
        .collect()
}

fn benches(c: &mut Criterion) {
    let xs = inputs();
    let mut group = c.benchmark_group(pasta_asm::BACKEND);
    group.throughput(Throughput::Elements(INPUTS as u64));
    group.bench_function("invert", |b| {
        b.iter(|| {
            for x in &xs {
                black_box(pasta_asm::invert(black_box(x), &MODULUS, INV, &V0));
            }
        })
    });
    pasta_asm::if_supported! {{
        let y = xs[1];
        group.bench_function("mul", |b| {
            b.iter(|| {
                for x in &xs {
                    black_box(pasta_asm::mul(black_box(x), &y, &MODULUS, INV));
                }
            })
        });
        group.bench_function("square", |b| {
            b.iter(|| {
                for x in &xs {
                    black_box(pasta_asm::square(black_box(x), &MODULUS, INV));
                }
            })
        });
    }}
    group.finish();
}

criterion_group!(group, benches);
criterion_main!(group);
