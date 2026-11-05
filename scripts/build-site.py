#!/usr/bin/env python3
"""Build the mathematical Blueprint as a static site."""
from __future__ import annotations

import argparse
from pathlib import Path
import shutil
import sys
import tempfile

from blueprint_paper import export_paper, load_paper, prepare_web_blueprint
from blueprint_computations import export_computations
from public_site import finish_public_site, normalize_graph_sources, publication_export
from hgraph.cli import _render_warning_summary, _SyncStyle
from hgraph.graph import Graph
from hgraph.site import write_from_manifest
from hgraph.sync import sync


ROOT = Path(__file__).resolve().parent.parent
STATE = ROOT / '.lake/blueprint'


def validate_output(out):
    """Limit replacement to generated output, outside sources and metadata."""
    out = out.resolve()
    root = ROOT.resolve()
    sources = ('site', 'scripts', 'blueprint', 'KIP126', 'AimPaper')
    authored = [(root / name).resolve() for name in sources]
    metadata = [(root / '.git').resolve(), STATE.resolve()]
    if out == (root / '.lake').resolve() or any(
            out == path or path in out.parents for path in metadata):
        raise ValueError('The output must be separate from repository metadata and build caches')
    if out == root or out in root.parents or any(
            out == path or path in out.parents for path in authored):
        raise ValueError('The output directory must be separate from authored sources')
    if (out.exists() and not out.is_dir()) or (out / '.git').exists():
        raise ValueError('The output must be a generated-site directory')
    marker = out / '.nojekyll'
    if out.exists() and any(out.iterdir()) and (
            not marker.is_file() or marker.is_symlink()):
        raise ValueError('Refusing to replace a nonempty directory without .nojekyll')
    return out


def stage_workspace(workspace):
    """Stage the Blueprint, Lean sources and graph settings."""
    project = workspace / 'Kervaire126'
    project.mkdir()
    shutil.copyfile(ROOT / 'config.yaml', workspace / 'config.yaml')
    (workspace / 'site').symlink_to(ROOT / 'site', target_is_directory=True)
    prepare_web_blueprint(ROOT, project / 'blueprint')
    (project / 'KIP126').symlink_to(ROOT / 'KIP126', target_is_directory=True)
    graph_dir = project / 'hgraph'
    graph_dir.mkdir()
    shutil.copyfile(ROOT / 'site/projects/Kervaire126/config.yaml', graph_dir / 'config.yaml')
    return project


def build_blueprint(out, *, verbose=False):
    """Build the mathematical reader and paper attachments."""
    with tempfile.TemporaryDirectory(prefix='workspace-', dir=STATE) as temporary:
        workspace = Path(temporary)
        project = stage_workspace(workspace)
        graph = Graph.open(project)
        report = sync(graph, blueprint=str(project / 'blueprint/content.tex'),
                      lean_paths=[project / 'KIP126'], root=project)
        normalize_graph_sources(graph)
        print(f'Native hgraph: {report["blueprint"]} mathematical entries, '
              f'{report["lean"]} Lean declarations, {len(report["warnings"])} warning(s).', flush=True)
        _render_warning_summary(report['warnings'], stream=sys.stdout,
                                style=_SyncStyle('auto', sys.stdout),
                                verbose=verbose, lean_count=report['lean'])
        with publication_export():
            write_from_manifest(workspace / 'config.yaml', out_path=out / 'index.html')
    export_paper(ROOT, out, load_paper(ROOT))
    export_computations(ROOT, out)
    proof_map = out / 'proof-map'
    proof_map.mkdir()
    for name in ('proof-map.html', 'proof-map.css', 'proof-map.js'):
        shutil.copyfile(ROOT / 'site' / name,
                        proof_map / ('index.html' if name.endswith('.html') else name))
    finish_public_site(out)


def build_site(out, *, verbose=False):
    """Build and atomically replace the static site."""
    out = validate_output(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    STATE.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix='.' + out.name + '-', dir=out.parent))
    assembled = temporary / 'site'
    previous = temporary / 'previous-site'
    published = False
    try:
        build_blueprint(assembled, verbose=verbose)
        (assembled / '.nojekyll').touch()

        if out.exists():
            out.rename(previous)
        try:
            assembled.rename(out)
        except Exception:
            if previous.exists() and not out.exists():
                previous.rename(out)
            raise
        published = True
    finally:
        # Retain the previous output when rollback fails.
        if published or not previous.exists():
            shutil.rmtree(temporary)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / '_site')
    parser.add_argument('--verbose', action='store_true',
                        help='Show every hgraph warning instead of three examples per category')
    args = parser.parse_args()
    print('Built', build_site(args.out, verbose=args.verbose), flush=True)


if __name__ == '__main__':
    main()
