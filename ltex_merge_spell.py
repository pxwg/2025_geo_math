#!/usr/bin/env python3
import os
from pathlib import Path


def merge_spell_words():
    # Path to Neovim spell file
    spell_file = Path.home() / ".config" / "nvim" / "spell" / "en.utf-8.add"
    current_file = Path(__file__).parent / ".ltex_dict" / "en-US.txt"

    # Read existing words from current file
    current_words = set()
    if os.path.exists(current_file):
        with open(current_file, "r", encoding="utf-8") as f:
            current_words = set(line.strip() for line in f if line.strip())

    # Read words from spell file
    spell_words = set()
    if spell_file.exists():
        with open(spell_file, "r", encoding="utf-8") as f:
            spell_words = set(line.strip() for line in f if line.strip())
    else:
        print(f"Spell file not found: {spell_file}")
        return

    # Find new words (not in current file)
    new_words = spell_words - current_words

    if new_words:
        # Append new words to current file
        with open(current_file, "a", encoding="utf-8") as f:
            for word in sorted(new_words):
                f.write(f"{word}\n")

        print(f"Added {len(new_words)} new words to {current_file}")
    else:
        print("No new words to add")


if __name__ == "__main__":
    merge_spell_words()
