\section{PKCS11}

\subsection{Checks}
\subsubsection{Template Complete}

Several functions in the API demands the template to be complete. It means that all the supplied attributes should be enough to construct an object. By the words all the supplied attributes we mean the set of attributes provided by a mechanism itself, the set of default attributes, and the set of attributes provided by the user. The required attributes are the attributes required by the type to create, and by the mechanism to run.
\\
In terms of code the functions have a logical precondition that the attribute is complete, and any function calling it, should satisfy the precondition. \\
A function to verify if this property is satisfied should provide a precondition stating that the template is complete. The check includes combining all the three types of attributes, getting a set of attributes required by a mechanism and checking whether all the required attributes are present.

For example, we are trying to create an ECDSA secret key. The required attributes are the attributes required by the mechanism $CKM_ECDSA$ combined with the attributes to create an instance of $CKO_SECRET_KEY$. The provided attributes are the user given attributes, default one (none for now), mechanism attributes (none for now). The function will satisfy if and only if in the provided attributes all the required ones are present.

\subsection{Key Generation}

The function $CKS_GenerateKey$ is the function that will be exposed to C. The function itself has the least preconditions possible: it takes a pure device (by the pure we mean that there is no precondition imposed on the device), a identifier of session (that's presented as uint32), pMechanism and pTemplate, also without any imposed properties. 

The function $__CKS_GenerateKey$ presents the main function executing key generation. It in turn requires some preconditions to be satisfied. So, the aim of the $_CKS_GenerateKey$ function is to check the preconditions, and if they are satisfied, to run the function. 