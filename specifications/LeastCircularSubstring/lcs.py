'''
This is an implementation of the Booth Least Circular Substrings algorithm.
To use the algorithm, import this module then call the lcs function with your
string. To run the property-based test, install Hypothesis and PyTest using
pip -r requirements.txt then run pytest lcs.py.
'''

def lcs(b):
    n = len(b)
    f = [-1] * (2 * n)
    k = 0
    for j in range(1, 2 * n):
        i = f[j - k - 1]
        while b[j % n] != b[(k + i + 1) % n] and i != -1:
            if b[j % n] < b[(k + i + 1) % n]:
                k = j - i - 1
            i = f[i]
        if b[j % n] != b[(k + i + 1) % n] and i == -1:
            if b[j % n] < b[(k + i + 1) % n]:
                k = j
            f[j - k] = -1
        else:
            f[j - k] = i + 1
    return k

def naive_lcs(s):
    n = len(s)
    if n == 0:
        return 0
    rotations = [s[i:] + s[:i] for i in range(n)]
    least_rotation = min(rotations)
    return rotations.index(least_rotation)

from hypothesis import given, settings
from hypothesis.strategies import text, sampled_from

@settings(max_examples=10000)
@given(text(sampled_from("abc")))
def test_lcs(b):
    assert lcs(b) == naive_lcs(b)

