#![feature(test)]

extern crate test;

use bimap::BiHashMap;
use test::{black_box, Bencher};

#[bench]
fn bench_hash_map_insert(b: &mut Bencher) {
    b.iter(|| {
        let mut map: BiHashMap<String, i64> = BiHashMap::new();

        for i in 1i64..100 {
            map.insert(format!("key {}", i), i);
        }

        black_box(map);
    });
}

#[bench]
fn bench_hash_map_insert_no_overwrite(b: &mut Bencher) {
    b.iter(|| {
        let mut map: BiHashMap<String, i64> = BiHashMap::new();

        for i in 1i64..100 {
            let _ = map.insert_no_overwrite(format!("key {}", i), i);
        }

        black_box(map);
    });
}

#[bench]
fn bench_hash_map_get_left(b: &mut Bencher) {
    let mut map: BiHashMap<String, i64> = BiHashMap::new();

    for i in 1i64..100 {
        map.insert(format!("key {}", i), i);
    }

    b.iter(|| {
        for i in 1i64..100 {
            black_box(map.get_by_left(&format!("key {}", i)));
        }
    });
}

#[bench]
fn bench_hash_map_get_right(b: &mut Bencher) {
    let mut map: BiHashMap<String, i64> = BiHashMap::new();

    for i in 1i64..100 {
        map.insert(format!("key {}", i), i);
    }

    b.iter(|| {
        for i in 1i64..100 {
            black_box(map.get_by_right(&i));
        }
    });
}

#[bench]
fn bench_hash_map_iter(b: &mut Bencher) {
    let mut map: BiHashMap<String, i64> = BiHashMap::new();

    for i in 1i64..100 {
        map.insert(format!("key {}", i), i);
    }

    b.iter(|| {
        map.iter().for_each(|(l, r)| {
            black_box((l, r));
        });
    });
}

#[bench]
fn bench_hash_map_replace_right(b: &mut Bencher) {
    let mut map: BiHashMap<String, i64> = BiHashMap::new();

    for i in 1i64..100 {
        map.insert(format!("key {}", i), i);
    }

    let mut y = 0;

    b.iter(|| {
        for i in 1i64..100 {
            black_box(map.insert(format!("key {}", i), y + i));
        }

        assert_eq!(map.len(), 99);

        y += 100;
    });
}

#[bench]
fn bench_hash_map_replace_left(b: &mut Bencher) {
    let mut map: BiHashMap<String, i64> = BiHashMap::new();

    for i in 1i64..100 {
        map.insert(format!("key {}", i), i);
    }

    let mut y = 0;

    b.iter(|| {
        for i in 1i64..100 {
            black_box(map.insert(format!("key {}", y + i), i));
        }

        assert_eq!(map.len(), 99);

        y += 100;
    });
}

#[bench]
fn bench_hash_map_replace_both(b: &mut Bencher) {
    let mut map: BiHashMap<String, i64> = BiHashMap::new();

    for i in 1i64..100 {
        map.insert(format!("key {}", i), i);
    }

    let mut order = true;

    b.iter(|| {
        for i in 1i64..100 {
            black_box(map.insert(format!("key {}", i), if order { i } else { 100 - i }));
        }

        assert_eq!(map.len(), 99);

        order = !order;
    });
}

#[bench]
fn bench_hash_map_replace_same(b: &mut Bencher) {
    let mut map: BiHashMap<String, i64> = BiHashMap::new();

    for i in 1i64..100 {
        map.insert(format!("key {}", i), i);
    }

    b.iter(|| {
        for i in 1i64..100 {
            black_box(map.insert(format!("key {}", i), i));
        }

        assert_eq!(map.len(), 99);
    });
}
