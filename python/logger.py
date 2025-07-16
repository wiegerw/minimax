# Copyright 2025 Wieger Wesselink.
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)


class LogSettings(object):
    enabled=False
    indent=0


def log(text: str):
    if LogSettings.enabled:
        print(' '*LogSettings.indent + text)
