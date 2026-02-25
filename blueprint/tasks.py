"""Tasks for building the Blueprint."""
from invoke import task
import os

BLUEPRINT_DIR = os.path.dirname(os.path.abspath(__file__))
SRC_DIR = os.path.join(BLUEPRINT_DIR, "src")


@task
def build(c):
    """Build the Blueprint PDF."""
    c.run(f"cd {SRC_DIR} && pdflatex -interaction=nonstopmode print.tex")


@task
def web(c):
    """Build the Blueprint web version."""
    c.run(f"cd {SRC_DIR} && python -m plastex web.tex")


@task
def clean(c):
    """Clean generated files."""
    c.run(f"cd {SRC_DIR} && rm -rf web tex put put.log *.aux *.toc *.out *.log")


@task
def serve(c, port=8080):
    """Serve the web version locally."""
    web_dir = os.path.join(SRC_DIR, "web")
    c.run(f"cd {web_dir} && python -m http.server {port}")
