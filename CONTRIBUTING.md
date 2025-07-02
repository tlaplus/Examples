# Contributing a Spec

Do you have a TLA⁺ specification you'd like to share with the community?
Your contribution would be greatly appreciated!
In addition to serving as an example, your spec will function as a powerful real-world test case for TLA⁺ language tooling.
The spec will also enjoy basic maintenance over the years, ensuring it remains functional & relevant as new features are added to TLA⁺ and its tools.

To ensure a high bar of quality, all specs in this repo are subject to automated continuous integration tests.
This means the spec contribution process has some amount of configuration & overhead, which can occasionally bring frustration.
If you are willing to push through this yourself that is greatly appreciated, but if it becomes an undue obstacle you can also add your spec directory to the [`.ciignore`](.ciignore) file to exclude your spec from validation; maintainers can then integrate it into the CI system at a later date.
Your spec must be contributed to the repository directly.
For reproducibility, contributing your spec as a git submodule is not supported.

Licensing your contributed specs under MIT is most appreciated, for consistency; however, other compatible permissive licenses are accepted.

## Basic Contribution Steps

1. Fork this repository and create a new directory under `specifications` with the name of your spec.
1. Place all TLA⁺ files in the directory, along with their `.cfg` model files.
1. You are encouraged to include at least one model that completes execution in less than 10 seconds, and (if possible) a model that fails in an interesting way - for example illustrating a system design you previously attempted that was found unsound by TLC.
1. Ensure the name of each `.cfg` file matches the `.tla` file it models, or has its name as a prefix; for example `SpecName.tla` can have the models `SpecName.cfg` and `SpecNameLiveness.cfg`.
   This makes it clear which model files are associated with which spec.
1. Include a `README.md` in the spec directory explaining the significance of the spec with links to any relevant websites or publications, or integrate this info as comments in the spec itself.

At this point, you have the option of adding your spec directory to the [`.ciignore`](.ciignore) file to simply contribute the spec files & exclude it from automated validation.
Contribution volume is low enough that maintainers will be able to onboard your spec to the validation process eventually.
However, if you are willing to put in the addition work of onboarding your spec to continuous integration yourself, follow the steps below.

## Adding Spec to Continuous Integration

All specs & models in this repository are subject to many validation checks; for a full listing, see [`DEVELOPING.md`](DEVELOPING.md).
While many of these checks concern basic properties like whether the spec parses properly and its models do not crash, they also check whether the spec correctly reflects metadata stored about it in [`manifest.json`](manifest.json) and a table in [`README.md`](README.md).

The central file containing metadata about all specs is [`manifest.json`](manifest.json).
You will need to add an entry to it for your spec & model files.
This can either be done manually (by looking at existing examples) or largely automated using the instructions below; note that if done manually you are very likely to miss tagging your spec with some feature flags detected & enforced by the CI.
Before submitted your changes to run in the CI, you can quickly check your [`manifest.json`](manifest.json) against the schema [`manifest-schema.json`](manifest-schema.json) at https://www.jsonschemavalidator.net/.
Steps:

1. Ensure you have Python 3.11+ installed; open a terminal in the root of this repository
1. It is considered best practice to create & initialize a Python virtual environment so the required packages are not installed globally; run `python -m venv .` then `source ./bin/activate` on Linux & macOS or `.\Scripts\activate.bat` on Windows (run `deactivate` to exit)
1. Run `pip install -r .github/scripts/requirements.txt`
1. Run `python .github/scripts/generate_manifest.py` to auto-generate your spec entry in [`manifest.json`](manifest.json) with as many details as possible
1. Locate your spec's entry in the [`manifest.json`](manifest.json) file and ensure the following fields are filled out:
   - Spec title: an appropriate title for your specification
   - Spec description: a short description of your specification
   - Spec sources: links relevant to the source of the spec (papers, blog posts, repositories)
   - Spec authors: a list of people who authored the spec
   - Spec tags:
     - `"beginner"` if your spec is appropriate for TLA⁺ newcomers
   - Model runtime: approximate model runtime on an ordinary workstation, in `"HH:MM:SS"` format
   - Model size:
     - `"small"` if the model can be executed in less than 10 seconds
     - `"medium"` if the model can be executed in less than five minutes
     - `"large"` if the model takes more than five minutes to execute
   - Model mode:
     - `"exhaustive search"` by default
     - `{"simulate": {"traceCount": N}}` for a simulation model
     - `"generate"` for model trace generation
     - `"symbolic"` for models checked using Apalache
   - Model result:
     - `"success"` if the model completes successfully
     - `"assumption failure"` if the model violates an assumption
     - `"safety failure"` if the model violates an invariant
     - `"liveness failure"` if the model fails to satisfy a liveness property
     - `"deadlock failure"` if the model encounters deadlock
   - (Optional) Model state count info: distinct states, total states, and state depth
     - These are all individually optional and only valid if your model uses exhaustive search and results in success
     - Recording these turns your model into a powerful regression test for TLC
   - Other fields are auto-generated by the script; if you are adding an entry manually, ensure their values are present and correct (see other entries or the [`manifest-schema.json`](manifest-schema.json) file)
1. Add your spec somewhere in the **topmost** table (not the bottom one, don't get them mixed up!) in [`README.md`](README.md); this must have:
   - The spec name as a link to the spec's directory, matching the name in the [`manifest.json`](manifest.json)
   - A comma-separated list of authors, which must also match the list of authors in [`manifest.json`](manifest.json)
   - A checkmark indicating whether the spec is appropriate for beginners
     - Checked IFF (if and only if) `beginner` is present in the `tags` field of your spec in [`manifest.json`](manifest.json)
   - A checkmark indicating whether the spec contains a formal proof
     - Checked IFF a `proof` tag is present in the `features` field of least one module under your spec in [`manifest.json`](manifest.json)
   - A checkmark indicating whether the spec contains PlusCal
     - Checked IFF a `pluscal` tag is present in the `features` field of least one module under your spec in [`manifest.json`](manifest.json)
   - A checkmark indicating whether the spec contains a TLC-checkable model
     - Checked IFF `exhaustive search`, `generate`, or `simulate` tags are present in the `mode` field of at least one model under your spec in [`manifest.json`](manifest.json)
   - A checkmark indicating whether the spec contains an Apalache-checkable model
     - Checked IFF `symbolic` tag is present in the `mode` field of at least one model under your spec in [`manifest.json`](manifest.json)

At this point you can open a pull request and the CI will run against your spec, alerting you to any details that you missed.
These scripts can be run locally for a faster development loop; see [`DEVELOPING.md`](DEVELOPING.md) for details.

