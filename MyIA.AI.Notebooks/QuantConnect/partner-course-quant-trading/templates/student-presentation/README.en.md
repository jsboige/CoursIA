# Student Presentation Template

## Usage

1. Copy `slides.md` into your project directory
2. Replace `[bracketed sections]` with your content
3. Add your charts (equity_curve.png, etc.) in the same directory
4. Launch the presentation:

```bash
npx slidev slides.md
```

## Required Sections

| Slide | Section | Expected Content |
|-------|---------|-----------------|
| 1 | Title | Strategy name, team |
| 2 | Outline | Table of contents |
| 3 | Introduction | Motivation, hypothesis |
| 4 | Data | Assets, period, preprocessing |
| 5 | Alpha model | Indicators, signals, risk management |
| 6-7 | Results | Equity curve + metrics |
| 8 | Analysis | Strengths/weaknesses, vs benchmark |
| 9 | Robustness | Sub-periods, sensitivity |
| 10 | Conclusion | Summary, improvements |

## Timing

- Target: 10 minutes +/- 1 minute
- ~1 minute per slide (10 content slides)
- Do not read slides: use keywords and speak naturally

## Tips

- Charts: always with legend, axis labels, and title
- Metrics: comparative table with benchmark
- Equity curve: with drawdown below
- Do not show code in slides (except short snippet for illustration)
