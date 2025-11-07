def require(p: bool):
    if not p:
        raise ValueError
