#!/usr/bin/env python3
"""
Generate interactive HTML analysis report from cluster results CSV.
Creates a self-contained HTML file with statistics, plots, and outlier detection.

Usage: python3 analyze_results.py results.csv [output.html]
"""

import pandas as pd
import numpy as np
import sys
import argparse
from pathlib import Path

def load_and_clean_data(csv_path):
    """Load CSV and convert boolean/numeric columns."""
    df = pd.read_csv(csv_path)

    # Convert boolean columns
    bool_cols = ['is_sat', 'is_unsat', 'has_proof', 'proof_truncated', 'has_error']
    for col in bool_cols:
        if col in df.columns:
            df[col] = df[col].map({'true': True, 'false': False})

    return df

def compute_reduction_ratios(df):
    """Add reduction ratio columns."""
    # Literal reduction
    df['literal_reduction_ratio'] = (
        (df['grim_cone_literals'] - df['grim_smol_literals']) /
        df['grim_cone_literals'].replace(0, np.nan)
    )

    # Constraint reduction
    df['constraint_reduction_ratio'] = (
        (df['inp_total_nbeq'] - df['grim_total_cone']) /
        df['inp_total_nbeq'].replace(0, np.nan)
    )

    # Size reduction
    df['size_reduction_ratio'] = (
        (df['inp_total_size'] - df['grim_total_size']) /
        df['inp_total_size'].replace(0, np.nan)
    )

    # Core reduction (if available)
    df['core_pattern_reduction'] = (
        (df['core_pattern_total'] - df['core_pattern_nodes']) /
        df['core_pattern_total'].replace(0, np.nan)
    )
    df['core_target_reduction'] = (
        (df['core_target_total'] - df['core_target_nodes']) /
        df['core_target_total'].replace(0, np.nan)
    )

    return df

def detect_outliers(df, column, method='iqr', threshold=3):
    """Detect outliers using IQR or z-score method."""
    if column not in df.columns or df[column].isna().all():
        return pd.Series([False] * len(df), index=df.index)

    data = df[column].dropna()

    if method == 'iqr':
        Q1 = data.quantile(0.25)
        Q3 = data.quantile(0.75)
        IQR = Q3 - Q1
        lower = Q1 - 1.5 * IQR
        upper = Q3 + 1.5 * IQR
        return (df[column] < lower) | (df[column] > upper)
    else:  # z-score
        mean = data.mean()
        std = data.std()
        z_scores = np.abs((df[column] - mean) / std)
        return z_scores > threshold

def generate_summary_stats(df):
    """Generate summary statistics tables."""
    stats = {}

    # Overall counts
    stats['overview'] = {
        'Total Instances': len(df),
        'SAT Instances': df['is_sat'].sum() if 'is_sat' in df.columns else 0,
        'UNSAT Instances': df['is_unsat'].sum() if 'is_unsat' in df.columns else 0,
        'With Proof': df['has_proof'].sum() if 'has_proof' in df.columns else 0,
        'Truncated': df['proof_truncated'].sum() if 'proof_truncated' in df.columns else 0,
        'Errors': df['has_error'].sum() if 'has_error' in df.columns else 0,
        'Resolv Iterations': df[df['resolv_iterations'] > 0].shape[0] if 'resolv_iterations' in df.columns else 0,
    }

    # Timing statistics (only for instances with proofs)
    proof_df = df[df['has_proof'] == True] if 'has_proof' in df.columns else df
    if not proof_df.empty:
        time_cols = ['grim_parse_time', 'grim_trim_time', 'grim_write_time', 'grim_total_time']
        stats['timing'] = {}
        for col in time_cols:
            if col in proof_df.columns and not proof_df[col].isna().all():
                stats['timing'][col] = {
                    'mean': proof_df[col].mean(),
                    'median': proof_df[col].median(),
                    'min': proof_df[col].min(),
                    'max': proof_df[col].max(),
                    'std': proof_df[col].std(),
                }

    # Reduction statistics
    if not proof_df.empty:
        reduction_cols = ['literal_reduction_ratio', 'constraint_reduction_ratio', 'size_reduction_ratio']
        stats['reduction'] = {}
        for col in reduction_cols:
            if col in proof_df.columns and not proof_df[col].isna().all():
                stats['reduction'][col] = {
                    'mean': proof_df[col].mean(),
                    'median': proof_df[col].median(),
                    'min': proof_df[col].min(),
                    'max': proof_df[col].max(),
                }

    return stats

def generate_html_report(df, stats, output_path):
    """Generate interactive HTML report using Plotly."""
    try:
        import plotly.graph_objects as go
        from plotly.subplots import make_subplots
        import plotly.express as px
    except ImportError:
        print("Error: plotly not installed. Run: pip install plotly pandas")
        sys.exit(1)

    # Filter to instances with proofs for most plots
    proof_df = df[df['has_proof'] == True].copy() if 'has_proof' in df.columns else df.copy()

    html_parts = []

    # HTML header
    html_parts.append("""
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>Proof Trimming Analysis Report</title>
    <script src="https://cdn.plot.ly/plotly-2.27.0.min.js"></script>
    <style>
        body {
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            margin: 20px;
            background: #f5f5f5;
        }
        .container {
            max-width: 1400px;
            margin: 0 auto;
            background: white;
            padding: 30px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        h1 {
            color: #2c3e50;
            border-bottom: 3px solid #3498db;
            padding-bottom: 10px;
        }
        h2 {
            color: #34495e;
            margin-top: 40px;
            border-bottom: 2px solid #ecf0f1;
            padding-bottom: 8px;
        }
        h3 {
            color: #7f8c8d;
            margin-top: 25px;
        }
        table {
            border-collapse: collapse;
            width: 100%;
            margin: 20px 0;
            background: white;
        }
        th, td {
            border: 1px solid #ddd;
            padding: 12px;
            text-align: left;
        }
        th {
            background-color: #3498db;
            color: white;
            font-weight: 600;
        }
        tr:nth-child(even) { background-color: #f8f9fa; }
        tr:hover { background-color: #e8f4f8; }
        .stat-box {
            display: inline-block;
            background: #ecf0f1;
            padding: 15px 25px;
            margin: 10px;
            border-radius: 6px;
            border-left: 4px solid #3498db;
        }
        .stat-label {
            font-size: 0.9em;
            color: #7f8c8d;
            font-weight: 500;
        }
        .stat-value {
            font-size: 1.8em;
            color: #2c3e50;
            font-weight: bold;
        }
        .outlier {
            background-color: #ffe5e5;
            font-weight: 600;
        }
        .warning {
            color: #e74c3c;
            font-weight: 600;
        }
        .success {
            color: #27ae60;
            font-weight: 600;
        }
        .plot-container {
            margin: 30px 0;
        }
    </style>
</head>
<body>
<div class="container">
<h1>📊 Proof Trimming Analysis Report</h1>
<p style="color: #7f8c8d; font-size: 0.95em;">
    Generated from cluster results • Total instances: """ + str(len(df)) + """
</p>
""")

    # Overview statistics
    html_parts.append("<h2>📈 Overview Statistics</h2>")
    html_parts.append('<div style="margin: 20px 0;">')
    for key, value in stats['overview'].items():
        html_parts.append(f'''
        <div class="stat-box">
            <div class="stat-label">{key}</div>
            <div class="stat-value">{value:,}</div>
        </div>
        ''')
    html_parts.append('</div>')

    # Skip reasons breakdown
    if 'skip_reason' in df.columns:
        skip_counts = df[df['skip_reason'].notna()]['skip_reason'].value_counts()
        if not skip_counts.empty:
            html_parts.append("<h3>Skip Reasons Breakdown</h3>")
            html_parts.append("<table>")
            html_parts.append("<tr><th>Reason</th><th>Count</th><th>Percentage</th></tr>")
            for reason, count in skip_counts.items():
                pct = (count / len(df)) * 100
                html_parts.append(f"<tr><td>{reason}</td><td>{count}</td><td>{pct:.1f}%</td></tr>")
            html_parts.append("</table>")

    # Error type breakdown
    if 'error_type' in df.columns:
        error_counts = df[df['has_error'] == True]['error_type'].value_counts()
        if not error_counts.empty:
            html_parts.append("<h3>Error Types</h3>")
            html_parts.append("<table>")
            html_parts.append("<tr><th>Error Type</th><th>Count</th></tr>")
            for err_type, count in error_counts.items():
                html_parts.append(f"<tr><td>{err_type}</td><td>{count}</td></tr>")
            html_parts.append("</table>")

    # Timing statistics
    if 'timing' in stats and stats['timing']:
        html_parts.append("<h2>⏱️ Timing Statistics (seconds)</h2>")
        html_parts.append("<table>")
        html_parts.append("<tr><th>Metric</th><th>Mean</th><th>Median</th><th>Min</th><th>Max</th><th>Std Dev</th></tr>")
        for metric, values in stats['timing'].items():
            html_parts.append(f'''
            <tr>
                <td>{metric.replace('_', ' ').title()}</td>
                <td>{values['mean']:.2f}</td>
                <td>{values['median']:.2f}</td>
                <td>{values['min']:.2f}</td>
                <td>{values['max']:.2f}</td>
                <td>{values['std']:.2f}</td>
            </tr>
            ''')
        html_parts.append("</table>")

    # Reduction statistics
    if 'reduction' in stats and stats['reduction']:
        html_parts.append("<h2>📉 Reduction Statistics</h2>")
        html_parts.append("<table>")
        html_parts.append("<tr><th>Metric</th><th>Mean</th><th>Median</th><th>Min</th><th>Max</th></tr>")
        for metric, values in stats['reduction'].items():
            html_parts.append(f'''
            <tr>
                <td>{metric.replace('_', ' ').title()}</td>
                <td>{values['mean']:.2%}</td>
                <td>{values['median']:.2%}</td>
                <td>{values['min']:.2%}</td>
                <td>{values['max']:.2%}</td>
            </tr>
            ''')
        html_parts.append("</table>")

    # Generate plots
    html_parts.append("<h2>📊 Interactive Visualizations</h2>")

    # Plot 1: Timing breakdown
    if not proof_df.empty and 'grim_parse_time' in proof_df.columns:
        fig1 = go.Figure()
        fig1.add_trace(go.Scatter(
            x=list(range(len(proof_df))),
            y=proof_df['grim_parse_time'],
            mode='markers',
            name='Parse Time',
            marker=dict(size=6, color='blue'),
            text=proof_df['instance'],
            hovertemplate='%{text}<br>Parse: %{y:.2f}s<extra></extra>'
        ))
        fig1.add_trace(go.Scatter(
            x=list(range(len(proof_df))),
            y=proof_df['grim_trim_time'],
            mode='markers',
            name='Trim Time',
            marker=dict(size=6, color='red'),
            text=proof_df['instance'],
            hovertemplate='%{text}<br>Trim: %{y:.2f}s<extra></extra>'
        ))
        fig1.add_trace(go.Scatter(
            x=list(range(len(proof_df))),
            y=proof_df['grim_write_time'],
            mode='markers',
            name='Write Time',
            marker=dict(size=6, color='green'),
            text=proof_df['instance'],
            hovertemplate='%{text}<br>Write: %{y:.2f}s<extra></extra>'
        ))
        fig1.update_layout(
            title='Timing Breakdown by Instance',
            xaxis_title='Instance Index',
            yaxis_title='Time (seconds)',
            yaxis_type='log',
            hovermode='closest',
            height=500
        )
        html_parts.append('<div class="plot-container">')
        html_parts.append(fig1.to_html(full_html=False, include_plotlyjs=False))
        html_parts.append('</div>')

    # Plot 2: Reduction scatter
    if not proof_df.empty and 'inp_total_nbeq' in proof_df.columns and 'grim_total_cone' in proof_df.columns:
        fig2 = go.Figure()
        fig2.add_trace(go.Scatter(
            x=proof_df['inp_total_nbeq'],
            y=proof_df['grim_total_cone'],
            mode='markers',
            marker=dict(
                size=8,
                color=proof_df['grim_total_time'] if 'grim_total_time' in proof_df.columns else 'blue',
                colorscale='Viridis',
                showscale=True,
                colorbar=dict(title='Total Time (s)')
            ),
            text=proof_df['instance'],
            hovertemplate='%{text}<br>Input: %{x}<br>Cone: %{y}<extra></extra>'
        ))
        # Add diagonal line
        max_val = max(proof_df['inp_total_nbeq'].max(), proof_df['grim_total_cone'].max())
        fig2.add_trace(go.Scatter(
            x=[0, max_val],
            y=[0, max_val],
            mode='lines',
            line=dict(dash='dash', color='gray'),
            name='No reduction',
            showlegend=True
        ))
        fig2.update_layout(
            title='Constraint Reduction: Input vs Cone',
            xaxis_title='Input Constraints',
            yaxis_title='Cone Constraints',
            xaxis_type='log',
            yaxis_type='log',
            height=500
        )
        html_parts.append('<div class="plot-container">')
        html_parts.append(fig2.to_html(full_html=False, include_plotlyjs=False))
        html_parts.append('</div>')

    # Plot 3: Literal reduction ratio histogram
    if not proof_df.empty and 'literal_reduction_ratio' in proof_df.columns:
        valid_ratios = proof_df['literal_reduction_ratio'].dropna()
        if not valid_ratios.empty:
            fig3 = go.Figure()
            fig3.add_trace(go.Histogram(
                x=valid_ratios * 100,
                nbinsx=30,
                marker=dict(color='lightblue', line=dict(color='darkblue', width=1))
            ))
            fig3.update_layout(
                title='Literal Reduction Ratio Distribution',
                xaxis_title='Reduction Ratio (%)',
                yaxis_title='Count',
                height=400
            )
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig3.to_html(full_html=False, include_plotlyjs=False))
            html_parts.append('</div>')

    # Outlier detection
    html_parts.append("<h2>🔍 Outlier Detection</h2>")

    outlier_cols = ['grim_total_time', 'grim_trim_time', 'literal_reduction_ratio']
    outliers_found = False

    for col in outlier_cols:
        if col in proof_df.columns:
            outliers = detect_outliers(proof_df, col)
            outlier_instances = proof_df[outliers]
            if not outlier_instances.empty:
                outliers_found = True
                html_parts.append(f"<h3>Outliers: {col.replace('_', ' ').title()}</h3>")
                html_parts.append("<table>")
                html_parts.append("<tr><th>Instance</th><th>Value</th><th>Mean</th><th>Deviation</th></tr>")
                col_mean = proof_df[col].mean()
                for idx, row in outlier_instances.iterrows():
                    deviation = ((row[col] - col_mean) / col_mean) * 100
                    html_parts.append(f'''
                    <tr class="outlier">
                        <td>{row['instance']}</td>
                        <td>{row[col]:.2f}</td>
                        <td>{col_mean:.2f}</td>
                        <td>{deviation:+.1f}%</td>
                    </tr>
                    ''')
                html_parts.append("</table>")

    if not outliers_found:
        html_parts.append("<p>No significant outliers detected.</p>")

    # Top 10 lists
    html_parts.append("<h2>🏆 Top 10 Lists</h2>")

    # Slowest instances
    if not proof_df.empty and 'grim_total_time' in proof_df.columns:
        slowest = proof_df.nlargest(10, 'grim_total_time')[['instance', 'grim_total_time', 'inp_total_nbeq', 'grim_total_cone']]
        html_parts.append("<h3>Slowest Instances (Total Time)</h3>")
        html_parts.append(slowest.to_html(index=False, classes='', border=0))

    # Largest reductions
    if not proof_df.empty and 'constraint_reduction_ratio' in proof_df.columns:
        best_reduction = proof_df.nlargest(10, 'constraint_reduction_ratio')[['instance', 'constraint_reduction_ratio', 'inp_total_nbeq', 'grim_total_cone']]
        html_parts.append("<h3>Best Constraint Reductions</h3>")
        html_parts.append(best_reduction.to_html(index=False, classes='', border=0, formatters={'constraint_reduction_ratio': lambda x: f'{x:.1%}'}))

    # Footer
    html_parts.append("""
</div>
</body>
</html>
""")

    # Write HTML file
    with open(output_path, 'w') as f:
        f.write('\n'.join(html_parts))

    print(f"✓ HTML report generated: {output_path}")
    print(f"  Open in browser to view interactive analysis")

def main():
    parser = argparse.ArgumentParser(description='Analyze proof trimming results and generate HTML report')
    parser.add_argument('csv_file', help='Input CSV file from aggregate_results.jl')
    parser.add_argument('output_html', nargs='?', default='analysis_report.html', help='Output HTML file')

    args = parser.parse_args()

    if not Path(args.csv_file).exists():
        print(f"Error: CSV file not found: {args.csv_file}")
        sys.exit(1)

    print(f"Loading data from {args.csv_file}...")
    df = load_and_clean_data(args.csv_file)

    print(f"Computing reduction ratios...")
    df = compute_reduction_ratios(df)

    print(f"Generating summary statistics...")
    stats = generate_summary_stats(df)

    print(f"Creating HTML report...")
    generate_html_report(df, stats, args.output_html)

    print(f"\n✓ Analysis complete!")
    print(f"  Total instances: {len(df)}")
    print(f"  With proofs: {df['has_proof'].sum() if 'has_proof' in df.columns else 'N/A'}")
    print(f"  Report: {args.output_html}")

if __name__ == '__main__':
    main()
