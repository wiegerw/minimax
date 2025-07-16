# Copyright 2025 Wieger Wesselink.
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

"""
Utility functions and settings for the minimax algorithm implementations.
"""

class MinimaxSettings(object):
    """
    Global settings for the minimax algorithm implementations.
    
    Attributes:
        stop_on_error: If True, errors will raise exceptions; if False, they will only print messages
        draw_node_ids: If True, node IDs will be included when drawing game trees
        draw_font_size: Font size to use when drawing game trees
        INFINITY: A large value representing infinity in the context of game evaluations
    """
    stop_on_error: bool = False
    draw_node_ids = False
    draw_font_size = 12
    INFINITY = 1000


def error(msg: str):
    """
    Handles error conditions based on the MinimaxSettings.stop_on_error setting.
    
    Args:
        msg: The error message to display
        
    Raises:
        RuntimeError: If MinimaxSettings.stop_on_error is True
    """
    print(msg)
    if MinimaxSettings.stop_on_error:
        raise RuntimeError('Stop on error')
