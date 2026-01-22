import csv
from collections import defaultdict
from statistics import median

def normalize_fieldnames(fieldnames):
    return {name.strip(): name for name in fieldnames}

def read_and_print_median_times(csv_path):
    # (threads, graph, algorithm, batch_size, batches_per_subiter) -> [times]
    grouped_times = defaultdict(list)

    with open(csv_path, newline='') as f:
        reader = csv.DictReader(f)
        field_map = normalize_fieldnames(reader.fieldnames)

        required = [
            "algorithm",
            "graph",
            "num_threads",
            "time (s)",
            "vgc_threshold",
            "batch_size",
            "batches_per_subiter",
        ]

        for col in required:
            if col not in field_map:
                raise KeyError(
                    f"Colonna '{col}' non trovata. "
                    f"Colonne disponibili: {reader.fieldnames}"
                )

        for row in reader:
            if int(row[field_map["vgc_threshold"]]) != 0:
                continue

            key = (
                int(row[field_map["num_threads"]]),
                row[field_map["graph"]].strip(),
                row[field_map["algorithm"]].strip(),
                int(row[field_map["batch_size"]]),
                int(row[field_map["batches_per_subiter"]]),
            )

            grouped_times[key].append(float(row[field_map["time (s)"]]))

    # riorganizzazione: threads -> graph -> algorithm -> risultati
    results = defaultdict(lambda: defaultdict(lambda: defaultdict(list)))

    for (threads, graph, algorithm, batch_size, batches_per_subiter), times in grouped_times.items():
        if not times:
            continue

        results[threads][graph][algorithm].append(
            (batch_size, batches_per_subiter, median(times))
        )

    # stampa ordinata
    for threads in sorted(results.keys()):
        print(f"\nThreads: {threads}")
        for graph in sorted(results[threads].keys()):
            print(f"  Graph: {graph}")
            for algorithm in sorted(results[threads][graph].keys()):
                print(f"    Algorithm: {algorithm}")
                for batch_size, batches_per_subiter, med_time in sorted(
                    results[threads][graph][algorithm],
                    key=lambda x: (x[0], x[1]),
                ):
                    print(
                        f"      batch_size={batch_size}, "
                        f"batches_per_subiter={batches_per_subiter} -> "
                        f"median time = {med_time:.6f} s"
                    )


if __name__ == "__main__":
    read_and_print_median_times("/home/sebastian/fastk/real_results/yes/results/pinning_strategies.csv")
