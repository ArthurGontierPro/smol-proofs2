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

    # Resolv iterations statistics
    if 'resolv_iterations' in df.columns:
        resolv_counts = df['resolv_iterations'].value_counts().sort_index()
        max_iter = df['resolv_iterations'].max()
        max_instances = df[df['resolv_iterations'] == max_iter]['instance'].tolist()
        stats['resolv'] = {
            'max': max_iter,
            'mean': df['resolv_iterations'].mean(),
            'counts': resolv_counts.to_dict(),
            'max_instances': max_instances
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

    # Trimmer timing statistics
    if 'timing' in stats and stats['timing']:
        html_parts.append("<h2>⏱️ Trimmer Times (seconds)</h2>")
        html_parts.append("<table>")
        html_parts.append("<tr><th>Metric</th><th>Mean</th><th>Median</th><th>Min</th><th>Max</th><th>Std Dev</th></tr>")
        timing_labels = {
            'grim_parse_time': 'Parse',
            'grim_trim_time': 'Trim',
            'grim_write_time': 'Write',
            'grim_total_time': 'Total'
        }
        for metric, values in stats['timing'].items():
            label = timing_labels.get(metric, metric.replace('_', ' ').title())
            html_parts.append(f'''
            <tr>
                <td>{label}</td>
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

    # Resolv iterations statistics
    if 'resolv' in stats and stats['resolv']:
        html_parts.append("<h2>🔄 Resolv Iterations</h2>")
        html_parts.append(f"<p><strong>Max:</strong> {stats['resolv']['max']}</p>")
        html_parts.append(f"<p><strong>Mean:</strong> {stats['resolv']['mean']:.2f}</p>")
        html_parts.append("<table>")
        html_parts.append("<tr><th>Iterations</th><th>Count</th></tr>")
        for iter_num in sorted(stats['resolv']['counts'].keys()):
            count = stats['resolv']['counts'][iter_num]
            html_parts.append(f"<tr><td>iter={iter_num}</td><td>{count} instance(s)</td></tr>")
        html_parts.append("</table>")
        if stats['resolv']['max_instances']:
            html_parts.append(f"<p><strong>Max instances:</strong> {', '.join(stats['resolv']['max_instances'][:5])}</p>")

    # Generate plots
    html_parts.append("<h2>📊 Interactive Visualizations</h2>")

    # Plot 1: Total proof size reduction
    html_parts.append("<h3>Total Proof Size Reduction</h3>")
    if not proof_df.empty and 'inp_total_size' in proof_df.columns and 'grim_total_size' in proof_df.columns:
        valid_data = proof_df[proof_df['inp_total_size'].notna() & proof_df['grim_total_size'].notna()]
        if not valid_data.empty:
            fig0a = go.Figure()
            fig0a.add_trace(go.Scatter(
                x=valid_data['inp_total_size'],
                y=valid_data['grim_total_size'],
                mode='markers',
                marker=dict(
                    size=4,
                    color=valid_data['grim_total_time'] if 'grim_total_time' in valid_data.columns else 'green',
                    colorscale='RdYlGn_r',
                    cmin=0,
                    cmax=6000,
                    showscale=True,
                    colorbar=dict(title='Time (s)'),
                    opacity=0.3
                ),
                text=valid_data['instance'],
                hovertemplate='%{text}<br>Input Size: %{x:,} bytes<br>Grim Size: %{y:,} bytes<extra></extra>'
            ))
            # Add diagonal line (no reduction)
            max_val = max(valid_data['inp_total_size'].max(), valid_data['grim_total_size'].max())
            fig0a.add_trace(go.Scatter(
                x=[1, max_val],
                y=[1, max_val],
                mode='lines',
                line=dict(dash='dash', color='gray', width=2),
                name='No reduction',
                showlegend=True,
                hoverinfo='skip'
            ))
            fig0a.update_layout(
                title='Total Proof Size Reduction: Input vs Trimmed',
                xaxis_title='Input Total Size (bytes)',
                yaxis_title='Trimmed Total Size (bytes)',
                xaxis_type='log',
                yaxis_type='log',
                hovermode='closest',
                height=500
            )
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig0a.to_html(full_html=False, include_plotlyjs='cdn'))
            html_parts.append('</div>')

    # Plot 2: OPB proof size reduction
    html_parts.append("<h3>OPB Proof Size Reduction</h3>")
    if not proof_df.empty and 'inp_opb_size' in proof_df.columns and 'grim_opb_size' in proof_df.columns:
        valid_data = proof_df[proof_df['inp_opb_size'].notna() & proof_df['grim_opb_size'].notna()]
        if not valid_data.empty:
            fig0b = go.Figure()
            fig0b.add_trace(go.Scatter(
                x=valid_data['inp_opb_size'],
                y=valid_data['grim_opb_size'],
                mode='markers',
                marker=dict(
                    size=4,
                    color=valid_data['grim_total_time'] if 'grim_total_time' in valid_data.columns else 'green',
                    colorscale='RdYlGn_r',
                    cmin=0,
                    cmax=6000,
                    showscale=True,
                    colorbar=dict(title='Time (s)'),
                    opacity=0.3
                ),
                text=valid_data['instance'],
                hovertemplate='%{text}<br>Input OPB: %{x:,} bytes<br>Grim OPB: %{y:,} bytes<extra></extra>'
            ))
            max_val = max(valid_data['inp_opb_size'].max(), valid_data['grim_opb_size'].max())
            fig0b.add_trace(go.Scatter(
                x=[1, max_val],
                y=[1, max_val],
                mode='lines',
                line=dict(dash='dash', color='gray', width=2),
                name='No reduction',
                showlegend=True,
                hoverinfo='skip'
            ))
            fig0b.update_layout(
                title='OPB File Size Reduction: Input vs Trimmed',
                xaxis_title='Input OPB Size (bytes)',
                yaxis_title='Trimmed OPB Size (bytes)',
                xaxis_type='log',
                yaxis_type='log',
                hovermode='closest',
                height=500
            )
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig0b.to_html(full_html=False, include_plotlyjs=False))
            html_parts.append('</div>')

    # Plot 3: PBP proof size reduction
    html_parts.append("<h3>PBP Proof Size Reduction</h3>")
    if not proof_df.empty and 'inp_pbp_size' in proof_df.columns and 'grim_pbp_size' in proof_df.columns:
        valid_data = proof_df[proof_df['inp_pbp_size'].notna() & proof_df['grim_pbp_size'].notna()]
        if not valid_data.empty:
            fig0c = go.Figure()
            fig0c.add_trace(go.Scatter(
                x=valid_data['inp_pbp_size'],
                y=valid_data['grim_pbp_size'],
                mode='markers',
                marker=dict(
                    size=4,
                    color=valid_data['grim_total_time'] if 'grim_total_time' in valid_data.columns else 'green',
                    colorscale='RdYlGn_r',
                    cmin=0,
                    cmax=6000,
                    showscale=True,
                    colorbar=dict(title='Time (s)'),
                    opacity=0.3
                ),
                text=valid_data['instance'],
                hovertemplate='%{text}<br>Input PBP: %{x:,} bytes<br>Grim PBP: %{y:,} bytes<extra></extra>'
            ))
            max_val = max(valid_data['inp_pbp_size'].max(), valid_data['grim_pbp_size'].max())
            fig0c.add_trace(go.Scatter(
                x=[1, max_val],
                y=[1, max_val],
                mode='lines',
                line=dict(dash='dash', color='gray', width=2),
                name='No reduction',
                showlegend=True,
                hoverinfo='skip'
            ))
            fig0c.update_layout(
                title='PBP File Size Reduction: Input vs Trimmed',
                xaxis_title='Input PBP Size (bytes)',
                yaxis_title='Trimmed PBP Size (bytes)',
                xaxis_type='log',
                yaxis_type='log',
                hovermode='closest',
                height=500
            )
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig0c.to_html(full_html=False, include_plotlyjs=False))
            html_parts.append('</div>')

    # Plot 4: Constraint reduction scatter
    html_parts.append("<h3>Constraint Reduction</h3>")
    if not proof_df.empty and 'inp_total_nbeq' in proof_df.columns and 'grim_total_cone' in proof_df.columns:
        valid_data = proof_df[proof_df['inp_total_nbeq'].notna() & proof_df['grim_total_cone'].notna()]
        if not valid_data.empty:
            fig1 = go.Figure()
            fig1.add_trace(go.Scatter(
                x=valid_data['inp_total_nbeq'],
                y=valid_data['grim_total_cone'],
                mode='markers',
                marker=dict(
                    size=4,
                    color=valid_data['grim_total_time'] if 'grim_total_time' in valid_data.columns else 'green',
                    colorscale='RdYlGn_r',
                    cmin=0,
                    cmax=6000,
                    showscale=True,
                    colorbar=dict(title='Time (s)'),
                    opacity=0.3
                ),
                text=valid_data['instance'],
                hovertemplate='%{text}<br>Input: %{x:,}<br>Cone: %{y:,}<extra></extra>'
            ))
            # Add diagonal line (no reduction)
            max_val = max(valid_data['inp_total_nbeq'].max(), valid_data['grim_total_cone'].max())
            fig1.add_trace(go.Scatter(
                x=[1, max_val],
                y=[1, max_val],
                mode='lines',
                line=dict(dash='dash', color='gray', width=2),
                name='No reduction',
                showlegend=True,
                hoverinfo='skip'
            ))
            fig1.update_layout(
                title='Constraint Reduction: Input vs Cone',
                xaxis_title='Input Constraints',
                yaxis_title='Cone Constraints',
                xaxis_type='log',
                yaxis_type='log',
                hovermode='closest',
                height=500
            )
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig1.to_html(full_html=False, include_plotlyjs='cdn'))
            html_parts.append('</div>')

    # Plot 2: Variable reduction scatter
    html_parts.append("<h3>Variable Reduction</h3>")
    if not proof_df.empty and 'inp_variables' in proof_df.columns and 'grim_cone_variables' in proof_df.columns:
        valid_data = proof_df[proof_df['inp_variables'].notna() & proof_df['grim_cone_variables'].notna()]
        if not valid_data.empty:
            fig2 = go.Figure()
            fig2.add_trace(go.Scatter(
                x=valid_data['inp_variables'],
                y=valid_data['grim_cone_variables'],
                mode='markers',
                marker=dict(
                    size=4,
                    color=valid_data['grim_total_time'] if 'grim_total_time' in valid_data.columns else 'green',
                    colorscale='RdYlGn_r',
                    cmin=0,
                    cmax=6000,
                    showscale=True,
                    colorbar=dict(title='Time (s)'),
                    opacity=0.3
                ),
                text=valid_data['instance'],
                hovertemplate='%{text}<br>Input Variables: %{x:,}<br>Cone Variables: %{y:,}<extra></extra>'
            ))
            # Add diagonal line (no reduction)
            max_val = max(valid_data['inp_variables'].max(), valid_data['grim_cone_variables'].max())
            fig2.add_trace(go.Scatter(
                x=[1, max_val],
                y=[1, max_val],
                mode='lines',
                line=dict(dash='dash', color='gray', width=2),
                name='No reduction',
                showlegend=True,
                hoverinfo='skip'
            ))
            fig2.update_layout(
                title='Variable Reduction: Input vs Cone',
                xaxis_title='Input Variables',
                yaxis_title='Cone Variables',
                xaxis_type='log',
                yaxis_type='log',
                hovermode='closest',
                height=500
            )
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig2.to_html(full_html=False, include_plotlyjs=False))
            html_parts.append('</div>')

    # Plot 3: Literal reduction scatter
    html_parts.append("<h3>Literal Reduction</h3>")
    if not proof_df.empty and 'inp_literals' in proof_df.columns and 'grim_cone_literals' in proof_df.columns:
        valid_data = proof_df[proof_df['inp_literals'].notna() & proof_df['grim_cone_literals'].notna()]
        if not valid_data.empty:
            fig3 = go.Figure()
            fig3.add_trace(go.Scatter(
                x=valid_data['inp_literals'],
                y=valid_data['grim_cone_literals'],
                mode='markers',
                marker=dict(
                    size=4,
                    color=valid_data['grim_total_time'] if 'grim_total_time' in valid_data.columns else 'green',
                    colorscale='RdYlGn_r',
                    cmin=0,
                    cmax=6000,
                    showscale=True,
                    colorbar=dict(title='Time (s)'),
                    opacity=0.3
                ),
                text=valid_data['instance'],
                hovertemplate='%{text}<br>Input Literals: %{x:,}<br>Cone Literals: %{y:,}<extra></extra>'
            ))
            # Add diagonal line (no reduction)
            max_val = max(valid_data['inp_literals'].max(), valid_data['grim_cone_literals'].max())
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
                title='Literal Reduction: Input vs Cone',
                xaxis_title='Input Literals',
                yaxis_title='Cone Literals',
                xaxis_type='log',
                yaxis_type='log',
                hovermode='closest',
                height=500
            )
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig3.to_html(full_html=False, include_plotlyjs=False))
            html_parts.append('</div>')

    # Plot 4: Core graph reduction scatter (Pattern)
    html_parts.append("<h3>Pattern Graph Core Reduction</h3>")
    if not proof_df.empty and 'pattern_vertices' in proof_df.columns and 'core_pattern_nodes' in proof_df.columns:
        valid_data = proof_df[proof_df['pattern_vertices'].notna() & proof_df['core_pattern_nodes'].notna()]
        if not valid_data.empty:
            fig4 = go.Figure()
            fig4.add_trace(go.Scatter(
                x=valid_data['pattern_vertices'],
                y=valid_data['core_pattern_nodes'],
                mode='markers',
                marker=dict(
                    size=4,
                    color=valid_data['grim_total_time'] if 'grim_total_time' in valid_data.columns else 'green',
                    colorscale='RdYlGn_r',
                    cmin=0,
                    cmax=6000,
                    showscale=True,
                    colorbar=dict(title='Time (s)'),
                    opacity=0.3
                ),
                text=valid_data['instance'],
                hovertemplate='%{text}<br>Pattern Vertices: %{x:,}<br>Core Vertices: %{y:,}<extra></extra>'
            ))
            # Add diagonal line (no reduction)
            max_val = max(valid_data['pattern_vertices'].max(), valid_data['core_pattern_nodes'].max())
            fig4.add_trace(go.Scatter(
                x=[1, max_val],
                y=[1, max_val],
                mode='lines',
                line=dict(dash='dash', color='gray', width=2),
                name='No reduction',
                showlegend=True,
                hoverinfo='skip'
            ))
            fig4.update_layout(
                title='Pattern Graph Core Reduction: Original vs Core',
                xaxis_title='Pattern Vertices',
                yaxis_title='Core Pattern Vertices',
                xaxis_type='log',
                yaxis_type='log',
                hovermode='closest',
                height=500
            )
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig4.to_html(full_html=False, include_plotlyjs=False))
            html_parts.append('</div>')

    # Plot 5: Target graph core reduction scatter
    html_parts.append("<h3>Target Graph Core Reduction</h3>")
    if not proof_df.empty and 'target_vertices' in proof_df.columns and 'core_target_nodes' in proof_df.columns:
        valid_data = proof_df[proof_df['target_vertices'].notna() & proof_df['core_target_nodes'].notna()]
        if not valid_data.empty:
            fig5 = go.Figure()
            fig5.add_trace(go.Scatter(
                x=valid_data['target_vertices'],
                y=valid_data['core_target_nodes'],
                mode='markers',
                marker=dict(
                    size=4,
                    color=valid_data['grim_total_time'] if 'grim_total_time' in valid_data.columns else 'green',
                    colorscale='RdYlGn_r',
                    cmin=0,
                    cmax=6000,
                    showscale=True,
                    colorbar=dict(title='Time (s)'),
                    opacity=0.3
                ),
                text=valid_data['instance'],
                hovertemplate='%{text}<br>Target Vertices: %{x:,}<br>Core Vertices: %{y:,}<extra></extra>'
            ))
            # Add diagonal line (no reduction)
            max_val = max(valid_data['target_vertices'].max(), valid_data['core_target_nodes'].max())
            fig5.add_trace(go.Scatter(
                x=[1, max_val],
                y=[1, max_val],
                mode='lines',
                line=dict(dash='dash', color='gray', width=2),
                name='No reduction',
                showlegend=True,
                hoverinfo='skip'
            ))
            fig5.update_layout(
                title='Target Graph Core Reduction: Original vs Core',
                xaxis_title='Target Vertices',
                yaxis_title='Core Target Vertices',
                xaxis_type='log',
                yaxis_type='log',
                hovermode='closest',
                height=500
            )
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig5.to_html(full_html=False, include_plotlyjs=False))
            html_parts.append('</div>')

    # Plot 6: Reduction ratio histograms
    html_parts.append("<h3>Reduction Ratio Distributions</h3>")
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

            fig6 = make_subplots(rows=1, cols=ncols, subplot_titles=titles)

            col_idx = 1
            if has_var:
                valid_ratios = proof_df['variable_reduction_ratio'].dropna()
                if not valid_ratios.empty:
                    fig6.add_trace(go.Histogram(
                        x=valid_ratios * 100,
                        nbinsx=30,
                        marker=dict(color='lightgreen', line=dict(color='darkgreen', width=1)),
                        name='Variable Reduction'
                    ), row=1, col=col_idx)
                    col_idx += 1

            if has_lit:
                valid_ratios = proof_df['literal_reduction_ratio'].dropna()
                if not valid_ratios.empty:
                    fig6.add_trace(go.Histogram(
                        x=valid_ratios * 100,
                        nbinsx=30,
                        marker=dict(color='lightblue', line=dict(color='darkblue', width=1)),
                        name='Literal Reduction'
                    ), row=1, col=col_idx)

            fig6.update_xaxes(title_text='Reduction Ratio (%)')
            fig6.update_yaxes(title_text='Count')
            fig6.update_layout(height=400, showlegend=False)
            html_parts.append('<div class="plot-container">')
            html_parts.append(fig6.to_html(full_html=False, include_plotlyjs=False))
            html_parts.append('</div>')

    # Instances with solver search (solver_nodes > 0)
    if not proof_df.empty and 'solver_nodes' in proof_df.columns:
        search_df = proof_df[proof_df['solver_nodes'] > 0]
        if not search_df.empty:
            html_parts.append("<h2>🔍 Instances with Solver Search</h2>")
            html_parts.append(f"<p>Showing {len(search_df):,} instances where solver performed search (solver_nodes > 0)</p>")

            # Helper function to create search plots
            def create_search_plot(df, x_col, y_col, title, x_label, y_label, hover_x, hover_y):
                valid_data = df[df[x_col].notna() & df[y_col].notna()]
                if not valid_data.empty:
                    fig = go.Figure()
                    fig.add_trace(go.Scatter(
                        x=valid_data[x_col],
                        y=valid_data[y_col],
                        mode='markers',
                        marker=dict(
                            size=4,
                            color=valid_data['solver_nodes'],
                            colorscale='RdYlGn_r',
                            showscale=True,
                            colorbar=dict(title='Solver Nodes'),
                            opacity=0.3
                        ),
                        text=valid_data['instance'],
                        hovertemplate=f'%{{text}}<br>{hover_x}: %{{x:,}}<br>{hover_y}: %{{y:,}}<br>Nodes: %{{marker.color:,}}<extra></extra>'
                    ))
                    max_val = max(valid_data[x_col].max(), valid_data[y_col].max())
                    fig.add_trace(go.Scatter(
                        x=[1, max_val],
                        y=[1, max_val],
                        mode='lines',
                        line=dict(dash='dash', color='gray', width=2),
                        name='No reduction',
                        showlegend=True,
                        hoverinfo='skip'
                    ))
                    fig.update_layout(
                        title=title,
                        xaxis_title=x_label,
                        yaxis_title=y_label,
                        xaxis_type='log',
                        yaxis_type='log',
                        hovermode='closest',
                        height=500
                    )
                    return fig
                return None

            # Total proof size reduction
            html_parts.append("<h3>Total Proof Size Reduction (Search Instances)</h3>")
            fig = create_search_plot(search_df, 'inp_total_size', 'grim_total_size',
                                    'Total Proof Size Reduction (Search Instances): Input vs Trimmed',
                                    'Input Total Size (bytes)', 'Trimmed Total Size (bytes)',
                                    'Input Size', 'Grim Size')
            if fig:
                html_parts.append('<div class="plot-container">')
                html_parts.append(fig.to_html(full_html=False, include_plotlyjs=False))
                html_parts.append('</div>')

            # OPB size reduction
            html_parts.append("<h3>OPB Proof Size Reduction (Search Instances)</h3>")
            fig = create_search_plot(search_df, 'inp_opb_size', 'grim_opb_size',
                                    'OPB File Size Reduction (Search Instances): Input vs Trimmed',
                                    'Input OPB Size (bytes)', 'Trimmed OPB Size (bytes)',
                                    'Input OPB', 'Grim OPB')
            if fig:
                html_parts.append('<div class="plot-container">')
                html_parts.append(fig.to_html(full_html=False, include_plotlyjs=False))
                html_parts.append('</div>')

            # PBP size reduction
            html_parts.append("<h3>PBP Proof Size Reduction (Search Instances)</h3>")
            fig = create_search_plot(search_df, 'inp_pbp_size', 'grim_pbp_size',
                                    'PBP File Size Reduction (Search Instances): Input vs Trimmed',
                                    'Input PBP Size (bytes)', 'Trimmed PBP Size (bytes)',
                                    'Input PBP', 'Grim PBP')
            if fig:
                html_parts.append('<div class="plot-container">')
                html_parts.append(fig.to_html(full_html=False, include_plotlyjs=False))
                html_parts.append('</div>')

            # Constraint reduction
            html_parts.append("<h3>Constraint Reduction (Search Instances)</h3>")
            fig = create_search_plot(search_df, 'inp_total_nbeq', 'grim_total_cone',
                                    'Constraint Reduction (Search Instances): Input vs Cone',
                                    'Input Constraints', 'Cone Constraints',
                                    'Input', 'Cone')
            if fig:
                html_parts.append('<div class="plot-container">')
                html_parts.append(fig.to_html(full_html=False, include_plotlyjs=False))
                html_parts.append('</div>')

            # Variable reduction
            html_parts.append("<h3>Variable Reduction (Search Instances)</h3>")
            fig = create_search_plot(search_df, 'inp_variables', 'grim_cone_variables',
                                    'Variable Reduction (Search Instances): Input vs Cone',
                                    'Input Variables', 'Cone Variables',
                                    'Input Variables', 'Cone Variables')
            if fig:
                html_parts.append('<div class="plot-container">')
                html_parts.append(fig.to_html(full_html=False, include_plotlyjs=False))
                html_parts.append('</div>')

            # Literal reduction
            html_parts.append("<h3>Literal Reduction (Search Instances)</h3>")
            fig = create_search_plot(search_df, 'inp_literals', 'grim_cone_literals',
                                    'Literal Reduction (Search Instances): Input vs Cone',
                                    'Input Literals', 'Cone Literals',
                                    'Input Literals', 'Cone Literals')
            if fig:
                html_parts.append('<div class="plot-container">')
                html_parts.append(fig.to_html(full_html=False, include_plotlyjs=False))
                html_parts.append('</div>')

            # Pattern graph core reduction
            html_parts.append("<h3>Pattern Graph Core Reduction (Search Instances)</h3>")
            fig = create_search_plot(search_df, 'pattern_vertices', 'core_pattern_nodes',
                                    'Pattern Graph Core Reduction (Search Instances): Original vs Core',
                                    'Pattern Vertices', 'Core Pattern Vertices',
                                    'Pattern Vertices', 'Core Vertices')
            if fig:
                html_parts.append('<div class="plot-container">')
                html_parts.append(fig.to_html(full_html=False, include_plotlyjs=False))
                html_parts.append('</div>')

            # Target graph core reduction
            html_parts.append("<h3>Target Graph Core Reduction (Search Instances)</h3>")
            fig = create_search_plot(search_df, 'target_vertices', 'core_target_nodes',
                                    'Target Graph Core Reduction (Search Instances): Original vs Core',
                                    'Target Vertices', 'Core Target Vertices',
                                    'Target Vertices', 'Core Vertices')
            if fig:
                html_parts.append('<div class="plot-container">')
                html_parts.append(fig.to_html(full_html=False, include_plotlyjs=False))
                html_parts.append('</div>')

    # Correlation: Solver Search vs Resolv Benefit
    if not proof_df.empty and 'solver_nodes' in proof_df.columns and 'resolv_iterations' in proof_df.columns:
        resolv_df = proof_df[proof_df['resolv_iterations'] > 0]
        if not resolv_df.empty and 'solver_nodes' in resolv_df.columns:
            valid_data = resolv_df[resolv_df['solver_nodes'].notna()]
            if not valid_data.empty:
                html_parts.append("<h2>🔗 Correlation: Solver Search vs Resolv Iterations</h2>")
                html_parts.append(f"<p>Analyzing {len(valid_data):,} instances with both solver search data and resolv iterations</p>")

                # Plot: solver_nodes vs resolv_iterations
                fig_corr = go.Figure()
                fig_corr.add_trace(go.Scatter(
                    x=valid_data['solver_nodes'],
                    y=valid_data['resolv_iterations'],
                    mode='markers',
                    marker=dict(
                        size=4,
                        color=valid_data['constraint_reduction_ratio'] if 'constraint_reduction_ratio' in valid_data.columns else 'blue',
                        colorscale='RdYlGn',
                        showscale=True,
                        colorbar=dict(title='Constraint<br>Reduction'),
                        opacity=0.5
                    ),
                    text=valid_data['instance'],
                    hovertemplate='%{text}<br>Solver Nodes: %{x:,}<br>Resolv Iters: %{y}<extra></extra>'
                ))
                fig_corr.update_layout(
                    title='Solver Search Nodes vs Resolv Iterations',
                    xaxis_title='Solver Nodes',
                    yaxis_title='Resolv Iterations',
                    xaxis_type='log',
                    hovermode='closest',
                    height=500
                )
                html_parts.append('<div class="plot-container">')
                html_parts.append(fig_corr.to_html(full_html=False, include_plotlyjs=False))
                html_parts.append('</div>')

                # Plot: constraint reduction for instances with/without resolv
                html_parts.append("<h3>Constraint Reduction: With vs Without Resolv</h3>")
                if 'constraint_reduction_ratio' in proof_df.columns:
                    no_resolv = proof_df[proof_df['resolv_iterations'] == 0]['constraint_reduction_ratio'].dropna()
                    with_resolv = proof_df[proof_df['resolv_iterations'] > 0]['constraint_reduction_ratio'].dropna()

                    if not no_resolv.empty and not with_resolv.empty:
                        from plotly.subplots import make_subplots
                        fig_comp = make_subplots(rows=1, cols=2, subplot_titles=('No Resolv', 'With Resolv'))

                        fig_comp.add_trace(go.Histogram(
                            x=no_resolv * 100,
                            nbinsx=30,
                            marker=dict(color='lightcoral', line=dict(color='darkred', width=1)),
                            name='No Resolv',
                            showlegend=False
                        ), row=1, col=1)

                        fig_comp.add_trace(go.Histogram(
                            x=with_resolv * 100,
                            nbinsx=30,
                            marker=dict(color='lightgreen', line=dict(color='darkgreen', width=1)),
                            name='With Resolv',
                            showlegend=False
                        ), row=1, col=2)

                        fig_comp.update_xaxes(title_text='Constraint Reduction (%)', row=1, col=1)
                        fig_comp.update_xaxes(title_text='Constraint Reduction (%)', row=1, col=2)
                        fig_comp.update_yaxes(title_text='Count', row=1, col=1)
                        fig_comp.update_yaxes(title_text='Count', row=1, col=2)
                        fig_comp.update_layout(height=400)

                        html_parts.append('<div class="plot-container">')
                        html_parts.append(f'<p>Mean without resolv: {no_resolv.mean():.1%} | Mean with resolv: {with_resolv.mean():.1%}</p>')
                        html_parts.append(fig_comp.to_html(full_html=False, include_plotlyjs=False))
                        html_parts.append('</div>')

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

    # Least reduced instances
    if not proof_df.empty and 'constraint_reduction_ratio' in proof_df.columns:
        worst_reduction = proof_df.nsmallest(10, 'constraint_reduction_ratio')[['instance', 'constraint_reduction_ratio', 'inp_total_nbeq', 'grim_total_cone']]
        html_parts.append("<h3>Least Reduced Instances</h3>")
        html_parts.append(worst_reduction.to_html(index=False, classes='', border=0, formatters={'constraint_reduction_ratio': lambda x: f'{x:.1%}'}))

    # Most reduced pattern graphs
    if not proof_df.empty and 'pattern_vertices' in proof_df.columns and 'core_pattern_nodes' in proof_df.columns:
        proof_df_copy = proof_df.copy()
        proof_df_copy['pattern_reduction_ratio'] = (
            (proof_df_copy['pattern_vertices'] - proof_df_copy['core_pattern_nodes']) /
            proof_df_copy['pattern_vertices'].replace(0, np.nan)
        )
        best_pattern = proof_df_copy.nlargest(10, 'pattern_reduction_ratio')[['instance', 'pattern_reduction_ratio', 'pattern_vertices', 'core_pattern_nodes']]
        html_parts.append("<h3>Most Reduced Pattern Graphs</h3>")
        html_parts.append(best_pattern.to_html(index=False, classes='', border=0, formatters={'pattern_reduction_ratio': lambda x: f'{x:.1%}'}))

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
