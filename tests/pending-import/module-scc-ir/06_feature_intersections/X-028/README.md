# X-028: Borrowed region escapes recursive result

A recursive operation returning a type whose exposed closure captures a rigid region fails ordinary capture/externality checks.

## Normative targets

* `§12.3`
* `§10.4.4.6`
