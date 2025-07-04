#!/usr/bin/env python3
"""
Script to update ltex_settings.json dictionary from .vscode/en-US.txt
"""

import json
import os
from pathlib import Path


def read_words_from_file(file_path):
    """Read words from a text file, one word per line."""
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            words = [line.strip() for line in f if line.strip()]
        return words
    except FileNotFoundError:
        print(f"Warning: {file_path} not found. Creating empty word list.")
        return []


def update_ltex_settings(words):
    """Update ltex_settings.json with the provided words."""
    settings_file = Path(
        "ltex_setting.json"
    )  # Note: using the actual filename from context

    # Create the updated settings structure
    updated_settings = {
        "ltex.dictionary": {
            "en-US": sorted(set(words))  # Remove duplicates and sort
        }
    }

    # Write to file with proper formatting
    with open(settings_file, "w", encoding="utf-8") as f:
        json.dump(updated_settings, f, indent=2, ensure_ascii=False)

    print(
        f"Updated {settings_file} with {len(updated_settings['ltex.dictionary']['en-US'])} words"
    )


def main():
    """Main function to orchestrate the update process."""
    vscode_dict_file = Path(".ltex_dict/en-US.txt")

    # Read words from .vscode/en-US.txt
    words = read_words_from_file(vscode_dict_file)

    # Update ltex_settings.json
    update_ltex_settings(words)


if __name__ == "__main__":
    main()
