## Modifications

### 28.02.2022

- Modified the way absorb function allocates a buffer. Instead of allocating a buffer of size rateInBytes, we now allocate the largest possible buffer (the largest rateInBytes) and then we cut a buffer we will be using (the size of rateInBytes). 
