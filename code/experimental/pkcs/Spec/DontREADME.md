% !TeX program = xelatex
% !TeX encoding = UTF-8 Unicode
% !BIB program = biber

\documentclass{relatorio}

\title{PhD Notes}
\addauthor{Anna Weine}
\setsubject{...}

\preamble{}
\addbibresource{bibliothek.bib}

\begin{document}
%   \input{abstract}
  
  \maketitle{}

\section{PKCS11}

\subsection{Checks}
\subsubsection{Template Complete}

Several functions in the API demands the template to be complete. It means that all the supplied attributes should be enough to construct an object. By the words all the supplied attributes we mean the set of attributes provided by a mechanism itself, the set of default attributes, and the set of attributes provided by the user. The required attributes are the attributes required by the type to create, and by the mechanism to run.
\\
In terms of code the functions have a logical precondition that the attribute is complete, and any function calling it, should satisfy the precondition. \\
A function to verify if this property is satisfied should provide a precondition stating that the template is complete. The check includes combining all the three types of attributes, getting a set of attributes required by a mechanism and checking whether all the required attributes are present. If functions computes that the template is not complete, the exception $CKR_TEMPLATE_INCOMPLETE$ is returned.
\\

For example, we are trying to create an ECDSA secret key. The required attributes are the attributes required by the mechanism $CKM_ECDSA$ combined with the attributes to create an instance of $CKO_SECRET_KEY$. The provided attributes are the user given attributes, default one (none for now), mechanism attributes (none for now). The function will satisfy if and only if in the provided attributes all the required ones are present. 

\subsubsection{Mechanism present of the device}

All the functions that use a mechanism should first check that the mechanism is indeed supported by the device. The check is done via requesting the device to provide the set of all supported mechanisms and verifying the presence of the concrete identifier in this set.
\\
In code all the functions that use a specific mechanism have the precondition $mechanismPresentOnDevice$. To be able to use the function, there should be a check for this precondition. The check includes getting all the supported mechanism from the device and verifying whether the requested mechanism is present. If the function computes that the mechanism is not present, the exception $CKR_MECHANISM_INVALID$ is returned.

\\ The main function returning the mechanism is mechanismGetFromDevice function, that returns a mechanism. The function requires the mechanism to be present, that could be verified as explained above. 

\\ For example, we are trying to create an ECDSA secret key. This requires the mechanism $CKM_EC_KEY_PAIR_GEN$ to be supported. 

\subsection{Key Generation}

The function $CKS_GenerateKey$ is the function that will be exposed to C. The function itself has the least preconditions possible: it takes a pure device (by the pure we mean that there is no precondition imposed on the device), a identifier of session (that's presented as uint32), pMechanism and pTemplate, also without any imposed properties. 

The function $__CKS_GenerateKey$ presents the main function executing key generation. It in turn requires some preconditions to be satisfied. So, the aim of the $_CKS_GenerateKey$ function is to check the preconditions, and if they are satisfied, to run the function. 


\end{document}
