The code in X64.AESCTR.vaf is derived from that shown in Figure 47 of

_Intel® Advanced Encryption Standard (AES) New Instructions Set_
Shay Gueron
Revision 3.0
May, 2010
https://www.intel.com/content/dam/doc/white-paper/advanced-encryption-standard-new-instructions-set-paper.pdf

The PDF ends with this information:

"INFORMATION IN THIS DOCUMENT IS PROVIDED IN CONNECTION WITH INTEL® PRODUCTS. NO LICENSE, EXPRESS OR IMPLIED,
BY ESTOPPEL OR OTHERWISE, TO ANY INTELLECTUAL PROPERTY RIGHTS IS GRANTED BY THIS DOCUMENT. EXCEPT AS PROVIDED
IN INTEL'S TERMS AND CONDITIONS OF SALE FOR SUCH PRODUCTS, INTEL ASSUMES NO LIABILITY WHATSOEVER, AND INTEL
DISCLAIMS ANY EXPRESS OR IMPLIED WARRANTY, RELATING TO SALE AND/OR USE OF INTEL PRODUCTS INCLUDING LIABILITY
OR WARRANTIES RELATING TO FITNESS FOR A PARTICULAR PURPOSE, MERCHANTABILITY, OR INFRINGEMENT OF ANY PATENT,
COPYRIGHT OR OTHER INTELLECTUAL PROPERTY RIGHT. Intel products are not intended for use in medical, life saving, life
sustaining, critical control or safety systems, or in nuclear facility applications.

Intel may make changes to specifications and product descriptions at any time, without notice. Designers must not rely on the
absence or characteristics of any features or instructions marked "reserved" or "undefined." Intel reserves these for future
definition and shall have no responsibility whatsoever for conflicts or incompatibilities arising from future changes to them. The
information here is subject to change without notice. Do not finalize a design with this information.

This specification, as well as the software described in it, is furnished under license and may only be used or copied in accordance
with the terms of the license. The information in this document is furnished for informational use only, is subject to change without
notice, and should not be construed as a commitment by Intel Corporation. Intel Corporation assumes no responsibility or liability
for any errors or inaccuracies that may appear in this document or any software that may be provided in association with this
document.

Intel processor numbers are not a measure of performance. Processor numbers differentiate features within each processor family,
not across different processor families. See www.intel.com/products/processor_number for details.

The Intel processor/chipset families may contain design defects or errors known as errata, which may cause the product to deviate
from published specifications. Current characterized errata are available on request.

Copies of documents, which have an order number and are referenced in this document, or other Intel literature, may be obtained
by calling 1-800-548-4725, or by visiting Intel's Web Site.

Intel and the Intel Logo are trademarks of Intel Corporation in the U.S. and other countries.

Other names and brands may be claimed as the property of others.
Copyright © 2010, Intel Corporation. All rights reserved. "
