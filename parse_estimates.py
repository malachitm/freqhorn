import csv
import re

features_to_match = [
    "Feature 1: Support any positive algebraic expression",
    "Feature 3: Support for loop guards",
    "Feature 4: Input variable"
]

results = {f: {"ids": [], "totals": [0.0]*8} for f in features_to_match}
any_partial = False

# Metric indices: 3: Human O, 4: Human ML, 5: Human P, 6: Human PERT, 7: AI O, 8: AI ML, 9: AI P, 10: AI PERT

with open('docs/feature1_subtask_estimates.csv', 'r') as f:
    text = f.read()
    # Normalize potential newlines within quoted fields or just split by row carefully
    # However the previous failure suggested 'inductive' was found where a number was expected.
    # Let's inspect the problematic line.
    
with open('docs/feature1_subtask_estimates.csv', 'r') as f:
    reader = csv.reader(f)
    header = next(reader)
    for row_idx, row in enumerate(reader):
        if not row: continue
        feature = row[0].strip()
        if feature not in features_to_match:
            continue
        
        # In some rows, status might be in a different index if commas are messed up
        # But let's look for Status by looking at the last few columns
        status = row[-1].strip().lower()
        if status == 'completed':
            continue
            
        subtask_id = row[1].strip()
        if status == 'partial':
            any_partial = True
            
        results[feature]["ids"].append(subtask_id)
        
        # Try to find exactly 8 floats in the row
        floats = []
        for val in row:
            val = val.strip()
            # Try to parse as float but ignore empty and non-numeric
            try:
                fval = float(val)
                floats.append(fval)
            except ValueError:
                pass
        
        # Typically the estimates are columns 3 to 10 (0-indexed)
        # However, let's just grab the first 8 floats after the first string column (feature) 
        # or just use fixed indices if possible.
        # Based on head output:
        # Col 0: Feature
        # Col 1: Sub-task #
        # Col 2: Sub-task Name
        # Col 3-10: Estimates
        
        for i in range(8):
            val = row[3+i].strip()
            try:
                results[feature]["totals"][i] += float(val)
            except ValueError:
                print(f"Error on row {row_idx+2}, col {3+i}: {val}")

grand_total = [0.0]*8
for f in features_to_match:
    print(f"{f}:")
    print(f"  Subtasks: {', '.join(results[f]['ids'])}")
    totals = [round(x, 2) for x in results[f]["totals"]]
    print(f"  Totals: {totals}")
    for i in range(8):
        grand_total[i] += results[f]["totals"][i]

print("-" * 20)
print(f"GRAND TOTAL: {[round(x, 2) for x in grand_total]}")
print(f"Any partial rows: {any_partial}")
