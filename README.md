# ISBN to MARC21 Converter

This repository contains a Python-based tool for automated conversion of
ISBN registration metadata into MARC21 bibliographic records.

## Features
- Converts Excel/CSV ISBN metadata into MARC21
- Outputs both:
  - `.mrc` (binary MARC21)
  - `.mrk` (human-readable MARC text)
- RDA-compliant field mapping
- Handles personal and corporate authors
- Supports batch processing

## Input
Metadata downloaded from https://isbn.gov.in including:
- Book title
- ISBN
- Author/Editor
- Publisher
- Language
- Product form
- Publication date

## Output
- `.mrc` for direct import into Koha and other ILS
- `.mrk` for validation and training

## How to run
```bash
pip install -r requirements.txt
python marc_ui.py
