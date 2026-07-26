# Arithmetic-certificate mutation contract

1. Compile `main.kp` and capture canonical KCoreText.
2. Verify the generated arithmetic certificate.
3. Mutate one field at a time: goal, assumption index/order, provider identity,
   provider version, domain version, context telescope, or canonical normal-form
   payload.
4. Each mutated artifact must be rejected with
   `E_KCORE_ARITHMETIC_CERTIFICATE_INVALID`.
5. No rejected artifact may reach KBackendIR.

Generation and canonical KCoreText round trips must be byte-stable for fixed
semantic inputs.
