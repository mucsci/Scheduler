# Security

## Reporting a vulnerability

Please **do not** open a public GitHub issue for security-sensitive reports.

Instead, use **[GitHub Security Advisories](https://github.com/mucsci/scheduler/security/advisories/new)** for this repository (or the Security tab → *Report a vulnerability*). We will work with you to understand and address the issue before any public disclosure.

## REST server expectations

The `scheduler-server` process does not implement API keys or user authentication. Deploy it only on trusted networks, or place it behind infrastructure that provides authentication, rate limiting, and appropriate request size limits. Schedule sessions are stored in memory and are cleared when the process stops.

For non-sensitive questions about deployment, open a regular GitHub issue on this repository.
