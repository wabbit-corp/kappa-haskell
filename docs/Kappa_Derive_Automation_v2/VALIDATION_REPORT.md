# Static validation report

* Test suite roots: **109**
* Kappa source files: **122**
* Incremental suites: **3**
* Multi-file non-incremental suites: **5**

## Result

All package-structure, manifest/file-list, module-path, directive-name, diagnostic-reference, delimiter-balance, UTF-8/LF,
Markdown-fence, and targeted source-syntax audits passed. The audit also checked that the patch contains the independent
evidence-uniqueness model, the `Eq -> Equiv` fallback bridge, dependent borrowed extensionality, and no
`expect term reflectsDec` declaration.

This is a static artifact audit. No Kappa compiler was available, so the suites were not typechecked or executed.
