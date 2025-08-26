# Installing

```commandline
pip install -e .
```

# Developing

The package is `nox` based. See `noxfile.py` for defined sessions (workflows).

## Running tests

Run tests with
```commandline
nox --session tests
```

Run tests faster by re-using the test environment.

```commandline
nox -r --session tests
```
