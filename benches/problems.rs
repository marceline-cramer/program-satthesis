use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

pub fn bench_from_directory(c: &mut Criterion, dir: &str) {
    let mut group = c.benchmark_group(dir);
    group.warm_up_time(std::time::Duration::from_millis(400));
    group.measurement_time(std::time::Duration::from_millis(800));
    group.sample_size(15);

    let mut paths = Vec::new();
    let dir = format!("./benches/problems/{dir}/");
    for file in std::fs::read_dir(&dir).unwrap() {
        let path = file.unwrap().path();
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let path = path.to_string_lossy().to_string();
        paths.push((name, path));
    }

    paths.sort();

    for (name, path) in paths {
        group.bench_with_input(BenchmarkId::from_parameter(name), &path, |b, path| {
            b.iter(|| program_satthesis::run(path, true));
        });
    }
}

pub fn random_20(c: &mut Criterion) {
    bench_from_directory(c, "random_20");
}

pub fn random_100(c: &mut Criterion) {
    bench_from_directory(c, "random_100");
}

pub fn random_250(c: &mut Criterion) {
    bench_from_directory(c, "random_250");
}

criterion_group!(benches, random_20, random_100, random_250);
criterion_main!(benches);
