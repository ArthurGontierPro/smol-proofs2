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

    # Convert boolean columns - handle both string and actual boolean
    bool_cols = ['is_sat', 'is_unsat', 'has_proof', 'proof_truncated', 'has_error']
    for col in bool_cols:
        if col in df.columns:
            # Handle both 'true'/'false' strings and actual True/False
            df[col] = df[col].map({'true': True, 'false': False, True: True, False: False, 'True': True, 'False': False})

    return df

def compute_reduction_ratios(df):
    """Add reduction ratio columns."""
    # Literal reduction
    df['literal_reduction_ratio'] = (
        (df['grim_cone_literals'] - df['grim_smol_literals']) /
        df['grim_cone_literals'].replace(0, np.nan)
    )

    # Variable reduction
    df['variable_reduction_ratio'] = (
        (df['inp_variables'] - df['grim_cone_variables']) /
        df['inp_variables'].replace(0, np.nan)
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
        'Successfully Trimmed': df['has_proof'].sum() if 'has_proof' in df.columns else 0,
        'Truncated Proofs': df['proof_truncated'].sum() if 'proof_truncated' in df.columns else 0,
        'Errors': df['has_error'].sum() if 'has_error' in df.columns else 0,
        'With Core Extraction': df[df['resolv_iterations'] > 0].shape[0] if 'resolv_iterations' in df.columns else 0,
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
        reduction_cols = ['variable_reduction_ratio', 'literal_reduction_ratio', 'constraint_reduction_ratio', 'size_reduction_ratio']
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

    # Plot 1: Parse time vs input size
    if not proof_df.empty and 'grim_parse_time' in proof_df.columns and 'inp_total_nbeq' in proof_df.columns:
        valid_data = proof_df[proof_df['inp_total_nbeq'].notna() & proof_df['grim_parse_time'].notna()]
        if not valid_data.empty:
            fig1 = go.Figure()
            fig1.add_trace(go.Scatter(
                x=valid_data['inp_total_nbeq'],
                y=valid_data['grim_parse_time'],
                mode='markers',
                marker=dict(size=6, color='blue', opacity=0.6),
                text=valid_data['instance'],
                hovertemplate='%{text}<br>Constraints: %{x:,}<br>Parse: %{y:.2f}s<extra></extra>'
            ))
            fig1.update_layout(
                title='Parse Time vs Input Size',
                xaxis_title='Input Constraints',
                yaxis_title='Parse Time (seconds)',
                xaxis_type='log',
                yaxis_type='log',
                hovermode='closest',
                height=450
            )
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig1.to_html(full_html=False, include_plotlyjs=False))
            html_parts.append('</div>')

    # Plot 2: Trim time vs input size
    if not proof_df.empty and 'grim_trim_time' in proof_df.columns and 'inp_total_nbeq' in proof_df.columns:
        valid_data = proof_df[proof_df['inp_total_nbeq'].notna() & proof_df['grim_trim_time'].notna()]
        if not valid_data.empty:
            fig2 = go.Figure()
            fig2.add_trace(go.Scatter(
                x=valid_data['inp_total_nbeq'],
                y=valid_data['grim_trim_time'],
                mode='markers',
                marker=dict(size=6, color='red', opacity=0.6),
                text=valid_data['instance'],
                hovertemplate='%{text}<br>Constraints: %{x:,}<br>Trim: %{y:.2f}s<extra></extra>'
            ))
            fig2.update_layout(
                title='Trim Time vs Input Size',
                xaxis_title='Input Constraints',
                yaxis_title='Trim Time (seconds)',
                xaxis_type='log',
                yaxis_type='log',
                hovermode='closest',
                height=450
            )
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig2.to_html(full_html=False, include_plotlyjs=False))
            html_parts.append('</div>')

    # Plot 3: Constraint reduction scatter
    if not proof_df.empty and 'inp_total_nbeq' in proof_df.columns and 'grim_total_cone' in proof_df.columns:
        valid_data = proof_df[proof_df['inp_total_nbeq'].notna() & proof_df['grim_total_cone'].notna()]
        if not valid_data.empty:
            fig3 = go.Figure()
            fig3.add_trace(go.Scatter(
                x=valid_data['inp_total_nbeq'],
                y=valid_data['grim_total_cone'],
                mode='markers',
                marker=dict(
                    size=6,
                    color=valid_data['grim_total_time'] if 'grim_total_time' in valid_data.columns else 'blue',
                    colorscale='Viridis',
                    showscale=True,
                    colorbar=dict(title='Total Time (s)'),
                    opacity=0.7
                ),
                text=valid_data['instance'],
                hovertemplate='%{text}<br>Input: %{x:,}<br>Cone: %{y:,}<extra></extra>'
            ))
            # Add diagonal line (no reduction)
            max_val = max(valid_data['inp_total_nbeq'].max(), valid_data['grim_total_cone'].max())
            fig3.add_trace(go.Scatter(
                x=[1, max_val],
                y=[1, max_val],
                mode='lines',
                line=dict(dash='dash', color='gray', width=2),
                name='No reduction',
                showlegend=True,
                hoverinfo='skip'
            ))
            fig3.update_layout(
                title='Constraint Reduction: Input vs Cone',
                xaxis_title='Input Constraints',
                yaxis_title='Cone Constraints',
                xaxis_type='log',
                yaxis_type='log',
                hovermode='closest',
                height=500
            )
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig3.to_html(full_html=False, include_plotlyjs=False))
            html_parts.append('</div>')

    # Plot 4: Variable and Literal reduction histograms side by side
    if not proof_df.empty:
        has_var = 'variable_reduction_ratio' in proof_df.columns
        has_lit = 'literal_reduction_ratio' in proof_df.columns

        if has_var or has_lit:
            from plotly.subplots import make_subplots
            ncols = (1 if has_var else 0) + (1 if has_lit else 0)
            titles = []
            if has_var:
                titles.append('Variable Reduction Distribution')
            if has_lit:
                titles.append('Literal Reduction Distribution')

            fig4 = make_subplots(rows=1, cols=ncols, subplot_titles=titles)

            col_idx = 1
            if has_var:
                valid_ratios = proof_df['variable_reduction_ratio'].dropna()
                if not valid_ratios.empty:
                    fig4.add_trace(go.Histogram(
                        x=valid_ratios * 100,
                        nbinsx=30,
                        marker=dict(color='lightgreen', line=dict(color='darkgreen', width=1)),
                        name='Variable Reduction'
                    ), row=1, col=col_idx)
                    col_idx += 1

            if has_lit:
                valid_ratios = proof_df['literal_reduction_ratio'].dropna()
                if not valid_ratios.empty:
                    fig4.add_trace(go.Histogram(
                        x=valid_ratios * 100,
                        nbinsx=30,
                        marker=dict(color='lightblue', line=dict(color='darkblue', width=1)),
                        name='Literal Reduction'
                    ), row=1, col=col_idx)

            fig4.update_xaxes(title_text='Reduction Ratio (%)')
            fig4.update_yaxes(title_text='Count')
            fig4.update_layout(height=400, showlegend=False)
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig4.to_html(full_html=False, include_plotlyjs=False))
            html_parts.append('</div>')

    # Plot 5: Core reduction (if available)
    if not proof_df.empty and 'core_pattern_reduction' in proof_df.columns:
        core_data = proof_df[proof_df['core_pattern_reduction'].notna()]
        if not core_data.empty:
            from plotly.subplots import make_subplots
            fig5 = make_subplots(rows=1, cols=2,
                                subplot_titles=('Pattern Graph Core Reduction', 'Target Graph Core Reduction'))

            # Pattern reduction
            fig5.add_trace(go.Histogram(
                x=core_data['core_pattern_reduction'] * 100,
                nbinsx=30,
                marker=dict(color='lightcoral', line=dict(color='darkred', width=1)),
                name='Pattern'
            ), row=1, col=1)

            # Target reduction
            if 'core_target_reduction' in core_data.columns:
                valid_target = core_data['core_target_reduction'].dropna()
                if not valid_target.empty:
                    fig5.add_trace(go.Histogram(
                        x=valid_target * 100,
                        nbinsx=30,
                        marker=dict(color='lightsalmon', line=dict(color='darkorange', width=1)),
                        name='Target'
                    ), row=1, col=2)

            fig5.update_xaxes(title_text='Core Reduction (%)')
            fig5.update_yaxes(title_text='Count')
            fig5.update_layout(height=400, showlegend=False)
            html_parts.append('<div class="plot-container">')
            html_parts.append('<h3>UNSAT Core Reductions</h3>')
            html_parts.append(fig5.to_html(full_html=False, include_plotlyjs=False))
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
