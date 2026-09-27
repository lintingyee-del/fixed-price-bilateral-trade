"""Export Figure 1 from the formalization supplement without redrawing it.

Documentation-only dependency: pip install pymupdf
Run from any directory with Python 3.11 or later.
"""
from pathlib import Path
import re

import fitz


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "research_ideas/probes/fixed_price/manuscript/formalization_supplement.pdf"
DESTINATION = ROOT / "docs/figures"
LABELS = ("A_model", "P_preliminaries", "P_energy", "P_reference", "P_gaps", "T_calibration")


def main():
    with fitz.open(SOURCE) as source:
        matches = [p.number for p in source if "Figure 1:" in p.get_text()
                   and "T_calibration" in p.get_text()]
        if len(matches) != 1:
            raise ValueError("Expected one page containing the dependency figure")
        page = source[matches[0]]
        caption_top = page.search_for("Figure 1:")[0].y0
        paths = [d["rect"] for d in page.get_drawings() if d["rect"].y1 < caption_top]
        if not paths:
            raise ValueError("No vector drawing found above the figure caption")
        bounds = fitz.Rect(paths[0])
        for rect in paths[1:]:
            bounds |= rect
        for label in LABELS:
            locations = [r for r in page.search_for(label) if r.y1 < caption_top]
            if len(locations) != 1:
                raise ValueError(f"Expected one figure label: {label}")
            bounds |= locations[0]
        bounds = fitz.Rect(bounds.x0 - 14, bounds.y0 - 14,
                           bounds.x1 + 14, bounds.y1 + 14) & page.rect
        DESTINATION.mkdir(parents=True, exist_ok=True)
        with fitz.open() as figure:
            target = figure.new_page(width=bounds.width, height=bounds.height)
            target.show_pdf_page(target.rect, source, page.number, clip=bounds)
            target.get_pixmap(matrix=fitz.Matrix(4, 4), alpha=False).save(
                DESTINATION / "theorem-c-dependency.png")
            svg = target.get_svg_image(text_as_path=True)
            # Keep the PDF's white background when displayed in dark-mode browsers.
            svg = re.sub(r"(<svg\b[^>]*>)", r'\1<rect width="100%" height="100%" fill="white"/>',
                         svg, count=1)
            (DESTINATION / "theorem-c-dependency.svg").write_text(svg, encoding="utf-8")
        print(f"Exported Figure 1 from PDF page {page.number + 1} to {DESTINATION}")


if __name__ == "__main__":
    main()
