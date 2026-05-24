import csv

features_to_track = [
    "Feature 1: Support any positive algebraic expression",
    "Feature 3: Support for loop guards",
    "Feature 4: Input variable"
]

totals = {f: {
    'Human O': 0.0, 'Human ML': 0.0, 'Human P': 0.0, 'Human PERT': 0.0,
    'AI O': 0.0, 'AI ML': 0.0, 'AI P': 0.0, 'AI PERT': 0.0,
    'subtasks': []
} for f in features_to_track}

with open('docs/feature1_subtask_estimates.csv', 'r') as f:
    reader = csv.DictReader(f)
    for row in reader:
        feature = row['Feature']
        if feature in features_to_track and row['Status'] != 'completed':
            try:
                totals[feature]['Human O'] += float(row['Human O (h)'])
                totals[feature]['Human ML'] += float(row['Human ML (h)'])
                totals[feature]['Human P'] += float(row['Human P (h)'])
                totals[feature]['Human PERT'] += float(row['Human PERT (h)'])
                totals[feature]['AI O'] += float(row['AI O (h)'])
                totals[feature]['AI ML'] += float(row['AI ML (h)'])
                totals[feature]['AI P'] += float(row['AI P (h)'])
                totals[feature]['AI PERT'] += float(row['AI PERT (h)'])
                totals[feature]['subtasks'].append(row['Sub-task #'])
            except ValueError:
                continue

for feature in features_to_track:
    print(f"--- {feature} ---")
    data = totals[feature]
    print(f"Included subtasks: {', '.join(data['subtasks'])}")
    print(f"Human: O={data['Human O']:.2f}, ML={data['Human ML']:.2f}, P={data['Human P']:.2f}, PERT={data['Human PERT']:.2f}")
    print(f"AI:    O={data['AI O']:.2f}, ML={data['AI ML']:.2f}, P={data['AI P']:.2f}, PERT={data['AI PERT']:.2f}")
    print()
