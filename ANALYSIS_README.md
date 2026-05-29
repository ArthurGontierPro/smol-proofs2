# Cluster Results Analysis Guide

## **Recommended Approaches for Presenting Results**

### 1. **Interactive HTML Report** (Best for Sharing)
**Tool**: `analyze_results.py` (included)

**Features**:
- ✅ Single self-contained HTML file
- ✅ Interactive plots (zoom, pan, hover for details)
- ✅ Automatic outlier detection
- ✅ Summary statistics tables
- ✅ No server needed - just open in browser
- ✅ Easy to share with collaborators

**Requirements**:
```bash
pip install plotly pandas
```

**Usage**:
```bash
python3 analyze_results.py cluster_results.csv report.html
```

**Output**: Generates `report.html` with:
- Overview statistics (counts, percentages)
- Skip reasons breakdown
- Timing statistics (mean, median, min, max)
- Reduction ratios (literal, constraint, size)
- Interactive scatter plots
- Outlier detection with instance names
- Top 10 slowest instances
- Top 10 best reductions

---

### 2. **Jupyter Notebook** (Best for Interactive Exploration)

Create `analysis.ipynb`:

```python
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns

# Load data
df = pd.read_csv('cluster_results.csv')

# Convert booleans
for col in ['is_sat', 'is_unsat', 'has_proof', 'has_error']:
    df[col] = df[col].map({'true': True, 'false': False})

# Filter to instances with proofs
proof_df = df[df['has_proof'] == True]

# Quick overview
print(f"Total instances: {len(df)}")
print(f"With proofs: {len(proof_df)}")
print(f"SAT: {df['is_sat'].sum()}")
print(f"Errors: {df['has_error'].sum()}")

# Plot timing distribution
proof_df['grim_total_time'].hist(bins=50, log=True)
plt.xlabel('Total Time (s)')
plt.ylabel('Count')
plt.title('Timing Distribution')
plt.show()

# Reduction scatter
plt.scatter(proof_df['inp_total_nbeq'],
            proof_df['grim_total_cone'],
            alpha=0.5)
plt.plot([0, proof_df['inp_total_nbeq'].max()],
         [0, proof_df['inp_total_nbeq'].max()],
         'r--', label='No reduction')
plt.xlabel('Input Constraints')
plt.ylabel('Cone Constraints')
plt.xscale('log')
plt.yscale('log')
plt.legend()
plt.title('Constraint Reduction')
plt.show()

# Outlier detection
Q1 = proof_df['grim_total_time'].quantile(0.25)
Q3 = proof_df['grim_total_time'].quantile(0.75)
IQR = Q3 - Q1
outliers = proof_df[
    (proof_df['grim_total_time'] < Q1 - 1.5*IQR) |
    (proof_df['grim_total_time'] > Q3 + 1.5*IQR)
]
print(f"\nTime Outliers ({len(outliers)}):")
print(outliers[['instance', 'grim_total_time']].to_string())
```

**Launch**:
```bash
jupyter notebook analysis.ipynb
```

---

### 3. **Static LaTeX Tables** (Best for Papers)

Generate LaTeX tables directly:

```python
import pandas as pd

df = pd.read_csv('cluster_results.csv')
proof_df = df[df['has_proof'].map({'true': True, 'false': False})]

# Summary table
summary = pd.DataFrame({
    'Metric': ['Total Instances', 'SAT', 'UNSAT', 'With Proof', 'Errors'],
    'Count': [
        len(df),
        df['is_sat'].map({'true': True, 'false': False}).sum(),
        df['is_unsat'].map({'true': True, 'false': False}).sum(),
        df['has_proof'].map({'true': True, 'false': False}).sum(),
        df['has_error'].map({'true': True, 'false': False}).sum(),
    ]
})

print(summary.to_latex(index=False))

# Timing statistics
timing_stats = proof_df[['grim_parse_time', 'grim_trim_time', 'grim_write_time']].describe()
print(timing_stats.to_latex())
```

Save to `tables.tex` and include in your paper.

---

### 4. **CSV Pivot Tables** (Excel/Google Sheets)

**For Collaborators Comfortable with Spreadsheets**:

1. Open `cluster_results.csv` in Excel/Google Sheets
2. Create pivot tables:
   - **By skip_reason**: Count instances per reason
   - **By error_type**: Count errors
   - **By runtime**: Bucket instances (0-10s, 10-60s, 60+s)
3. Create charts:
   - Histogram: `grim_total_time`
   - Scatter: `inp_total_nbeq` vs `grim_total_cone`
   - Bar chart: Skip reasons

**Advantage**: No programming needed, familiar interface

---

### 5. **Custom Dashboard with Streamlit** (Best for Live Demos)

Create `dashboard.py`:

```python
import streamlit as st
import pandas as pd
import matplotlib.pyplot as plt

st.title("Proof Trimming Analysis Dashboard")

df = pd.read_csv('cluster_results.csv')

# Sidebar filters
st.sidebar.header("Filters")
show_sat = st.sidebar.checkbox("Include SAT", value=True)
min_time = st.sidebar.slider("Min time (s)", 0.0, 100.0, 0.0)

# Filter data
filtered = df.copy()
if not show_sat:
    filtered = filtered[filtered['is_sat'] != 'true']
filtered = filtered[filtered['grim_total_time'] >= min_time]

# Display stats
st.metric("Total Instances", len(filtered))
st.metric("Mean Trim Time", f"{filtered['grim_trim_time'].mean():.2f}s")

# Plot
fig, ax = plt.subplots()
ax.hist(filtered['grim_total_time'], bins=30)
ax.set_xlabel('Time (s)')
ax.set_ylabel('Count')
st.pyplot(fig)

# Data table
st.dataframe(filtered[['instance', 'grim_total_time', 'grim_total_cone']])
```

**Launch**:
```bash
pip install streamlit
streamlit run dashboard.py
```

Access at `http://localhost:8501` - great for live presentations!

---

## **Recommended Workflow**

For your use case (sharing with collaborators + record keeping):

1. **Generate HTML Report** (Primary)
   ```bash
   python3 analyze_results.py cluster_results.csv analysis_report.html
   ```
   - Share `analysis_report.html` via email/web
   - Self-contained, works offline
   - Interactive exploration

2. **Create Jupyter Notebook** (Secondary - for deep analysis)
   - Keep in git repository
   - Document specific findings
   - Generate paper figures

3. **Archive Raw CSV** (Record)
   - Keep `cluster_results.csv` in git with timestamp
   - Add summary to commit message
   - Tag important runs

4. **Extract Key Tables for Papers**
   - Use LaTeX table generation
   - Create summary tables
   - Highlight best/worst cases

---

## **Outlier Detection Methods**

### IQR Method (Recommended)
```python
Q1 = df[col].quantile(0.25)
Q3 = df[col].quantile(0.75)
IQR = Q3 - Q1
outliers = (df[col] < Q1 - 1.5*IQR) | (df[col] > Q3 + 1.5*IQR)
```

### Z-Score Method
```python
mean = df[col].mean()
std = df[col].std()
outliers = abs((df[col] - mean) / std) > 3
```

---

## **Key Metrics to Report**

### Performance
- Median trim time
- 95th percentile trim time
- Speedup vs baseline (if available)

### Reduction Quality
- Median constraint reduction ratio
- Median literal reduction ratio
- Median size reduction (bytes)

### Reliability
- Success rate (has_proof / total)
- Error rate by type
- Truncation rate

### Scalability
- Time vs input size correlation
- Memory usage (from OOM events)
- Largest successfully trimmed instance

---

## **Git Integration**

Add to your repository:
```bash
git add cluster_results.csv analysis_report.html
git commit -m "results: cluster run 2026-05-29

- 2280 instances processed
- X% success rate
- Median trim time: Ys
- See analysis_report.html for details"
git tag cluster-run-2026-05-29
```

This creates a permanent record with easy access to the report.
