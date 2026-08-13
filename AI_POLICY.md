# TLA+ Examples AI Usage Policy

The TLA+ Examples project has strict rules for AI usage:

- **All AI usage in any form must be disclosed.** You must state the tool you
used (e.g. Codex, Claude Code, Cursor, Copilot) along with the extent that the
work was AI-assisted.

- **The human-in-the-loop must fully understand all TLA+ they contribute.** If
you can't explain what your specification does and how it models the system
without the aid of AI tools, do not contribute it to this project.

  In particular, if you are new to TLA+, you must be able to explain all TLA+
  constructs in your contribution. AI tools are great helpers for learning. Use
  them to understand your specification.

- **Issues and discussions must be written by humans.** AI tools are good at
producing lengthy prose, but this prose is hard to read for humans. We prefer
text that demonstrates human reasoning. It is okay to have spelling and grammar
mistakes, as long as you have put some thinking into your writing.

  If you use AI to do research, you may quote the results of that research in a
  clearly marked blockquote. However, you must verify the results before quoting
  them, and you must trim the results down to the relevant information.

- **Descriptions of Pull Requests must be written by humans.** Pull requests
should specify: the intent of the change, the key design decisions, the parts of
the specification or repository affected, and the key changes (briefly). The
size of the PR text must be proportional to the size of the change. A small
change does not need a 5-page description.

- **No AI-generated media is allowed (art, images, videos, audio, etc.).** Text,
TLA+ specifications, and code are the only acceptable AI-generated content, per
the other rules in this policy.

- **Review capacity is the bottleneck of this project.** Do not assume your Pull
Request will be reviewed, however sound it is. It has to be compelling enough
that a maintainer chooses to spend their time on it, so open the contributions
that matter most, not everything you can produce.

- **Signed-off-by and Developer Certificate of Origin.** AI agents MUST NOT add
Signed-off-by tags. Only humans can legally certify the Developer Certificate of
Origin (DCO). The human submitter is responsible for:

  - Reviewing all AI-generated content

  - Ensuring compliance with licensing requirements

  - Adding their own Signed-off-by tag to certify the DCO

  - Taking full responsibility for the contribution

  Moreover, read the [LF Guidance on Generative AI][lf-generative-ai] to
  understand the copyright and licensing implications of using AI tools.

**The above rules apply only to outside contributions to TLA+ Examples**. Maintainers
are exempt from these rules and may use AI tools at their discretion. They have
proven themselves trustworthy to apply good judgment.

## There are Humans Here

Please remember that TLA+ Examples is maintained by humans. The specifications in this
repository have been written and curated by humans. This means that many specification,
modeling, and repository decisions do not follow the canned recipes of the AI tools.
Due to that, the AI tools may fail to understand the intent behind a specification.

Every discussion, issue, and pull request is read and reviewed by humans (and
sometimes machines, too). It is a boundary point at which people interact with
each other and the work done. It is rude and disrespectful to approach this
boundary with low-effort, unqualified work, since it puts the burden of
validation on the maintainers. Most of the time, the maintainers are not paid
for doing this work, and they aim at improving the project quality, not reading
the inference of AI tools.

## AI is Welcome Here

The maintainers of TLA+ Examples embrace the use of AI. We are careful about
the specifications in this repository, as they have been written and curated by
humans, who put plenty of their thought into them.

**Our reason for the strict AI policy is not due to an anti-AI stance**. We
understand that many external contributors are trying to help the project. We
also know that it is tempting to shoot an AI tool at a problem and see it
"solved". Unfortunately, the AI tools do not have understanding of the impact
of their output. We may see TLA+ that appears to solve the problem or correctly
specify a system, but is not properly understood by the contributor, integrated
into the repository, or tested. As a result, the maintainers can have to spend
hours of their time validating or fixing work that was generated in minutes.

## References

This policy is adapted from the [Apalache AI Usage Policy][apalache-ai-policy],
which derives from the following AI policies and guidelines:

 - Large parts of the [Ghostty AI Policy][ghostty-ai-policy]
 - [Linux Foundation Generative AI Policy][lf-generative-ai]
 - [Kernel Coding Assistants][kernel-coding-assistants]

[apalache-ai-policy]: https://github.com/apalache-mc/apalache/blob/main/AI_POLICY.md
[ghostty-ai-policy]: https://github.com/ghostty-org/ghostty/blob/main/AI_POLICY.md
[lf-generative-ai]: https://www.linuxfoundation.org/legal/generative-ai
[kernel-coding-assistants]: https://kernel.org/doc/html/next/process/coding-assistants.html
