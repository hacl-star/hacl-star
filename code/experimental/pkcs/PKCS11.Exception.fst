module PKCS11.Exception

open PKCS11.TypeDeclaration

type exp_ckr_general = 
	| CKR_GENERAL_ERROR: exp_ckr_general
	| CKR_HOST_MEMORY: exp_ckr_general
	| CKR_FUNCTION_FAILED:  exp_ckr_general

type exp_ckr_session = 
	|CKR_SESSION_HANDLE_INVALID: exp_ckr_session
	|CKR_DEVICE_REMOVED_Session: exp_ckr_session
	|CKR_SESSION_CLOSED: exp_ckr_session

type exp_ckr_token = 
	|CKR_DEVICE_MEMORY: exp_ckr_token 
	|CKR_DEVICE_ERROR: exp_ckr_token
	|CKR_TOKEN_NOT_PRESENT: exp_ckr_token
	|CKR_DEVICE_REMOVED_Token: exp_ckr_token

type exp_ckr_callback = 
	| CKR_CANCEL: exp_ckr_callback

type exp_ckr_mutex = 
	|CKR_MUTEX_BAD: exp_ckr_mutex
	|CKR_MUTEX_NOT_LOCKED: exp_ckr_mutex

type exp_ckr_other = 
	|CKR_ACTION_PROHIBITED: exp_ckr_other
	|CKR_ARGUMENTS_BAD: exp_ckr_other
	|CKR_ATTRIBUTE_READ_ONLY: exp_ckr_other
	|CKR_ATTRIBUTE_SENSITIVE: exp_ckr_other
	|CKR_ATTRIBUTE_TYPE_INVALID: exp_ckr_other
	|CKR_ATTRIBUTE_VALUE_INVALID: exp_ckr_other
	|CKR_BUFFER_TOO_SMALL: exp_ckr_other
	|CKR_CANT_LOCK: exp_ckr_other
	|CKR_CRYPTOKI_ALREADY_INITIALIZED: exp_ckr_other
	|CKR_CRYPTOKI_NOT_INITIALIZED: exp_ckr_other
	|CKR_CURVE_NOT_SUPPORTED: exp_ckr_other
	|CKR_DATA_INVALID: exp_ckr_other
	|CKR_DATA_LEN_RANGE: exp_ckr_other
	|CKR_DOMAIN_PARAMS_INVALID: exp_ckr_other
	|CKR_ENCRYPTED_DATA_INVALID: exp_ckr_other
	|CKR_ENCRYPTED_DATA_LEN_RANGE:  exp_ckr_other
	|CKR_EXCEEDED_MAX_ITERATIONS: exp_ckr_other
	|CKR_FIPS_SELF_TEST_FAILED: exp_ckr_other
	|CKR_FUNCTION_CANCELED: exp_ckr_other
	|CKR_FUNCTION_NOT_PARALLEL: exp_ckr_other
	|CKR_FUNCTION_NOT_SUPPORTED: exp_ckr_other
	|CKR_FUNCTION_REJECTED:  exp_ckr_other
	|CKR_INFORMATION_SENSITIVE: exp_ckr_other
	|CKR_KEY_CHANGED: exp_ckr_other
	|CKR_KEY_FUNCTION_NOT_PERMITTED: exp_ckr_other
	|CKR_KEY_HANDLE_INVALID: exp_ckr_other
	|CKR_KEY_INDIGESTIBLE: exp_ckr_other
	|CKR_KEY_NEEDED: exp_ckr_other
	|CKR_KEY_NOT_NEEDED: exp_ckr_other
	|CKR_KEY_NOT_WRAPPABLE: exp_ckr_other
	|CKR_KEY_SIZE_RANGE:  exp_ckr_other
	|CKR_KEY_TYPE_INCONSISTENT: exp_ckr_other
	|CKR_KEY_UNEXTRACTABLE: exp_ckr_other
	|CKR_LIBRARY_LOAD_FAILED: exp_ckr_other
	|CKR_MECHANISM_INVALID: exp_ckr_other
	|CKR_MECHANISM_PARAM_INVALID:  exp_ckr_other
	|CKR_NEED_TO_CREATE_THREADS: exp_ckr_other
	|CKR_NO_EVENT: exp_ckr_other
	|CKR_OBJECT_HANDLE_INVALID: exp_ckr_other
	|CKR_OPERATION_ACTIVE:  exp_ckr_other
	|CKR_OPERATION_NOT_INITIALIZED: exp_ckr_other
	|CKR_PIN_EXPIRED: exp_ckr_other
	|CKR_PIN_INCORRECT: exp_ckr_other
	|CKR_PIN_INVALID: exp_ckr_other
	|CKR_PIN_LEN_RANGE: exp_ckr_other
	|CKR_PIN_LOCKED:  exp_ckr_other
	|CKR_PIN_TOO_WEAK: exp_ckr_other
	|CKR_PUBLIC_KEY_INVALID:  exp_ckr_other
	|CKR_RANDOM_NO_RNG:  exp_ckr_other
	|CKR_RANDOM_SEED_NOT_SUPPORTED: exp_ckr_other
	|CKR_SAVED_STATE_INVALID:  exp_ckr_other
	|CKR_SESSION_COUNT: exp_ckr_other
	|CKR_SESSION_EXISTS: exp_ckr_other
	|CKR_SESSION_PARALLEL_NOT_SUPPORTED: exp_ckr_other
	|CKR_SESSION_READ_ONLY: exp_ckr_other
	|CKR_SESSION_READ_ONLY_EXISTS: exp_ckr_other
	|CKR_SESSION_READ_WRITE_SO_EXISTS: exp_ckr_other
	|CKR_SIGNATURE_LEN_RANGE: exp_ckr_other
	|CKR_SIGNATURE_INVALID: exp_ckr_other
	|CKR_SLOT_ID_INVALID: exp_ckr_other
	|CKR_STATE_UNSAVEABLE: exp_ckr_other
	|CKR_TEMPLATE_INCOMPLETE:  exp_ckr_other
	|CKR_TEMPLATE_INCONSISTENT:  exp_ckr_other
	|CKR_TOKEN_NOT_RECOGNIZED:  exp_ckr_other
	|CKR_TOKEN_WRITE_PROTECTED: exp_ckr_other
	|CKR_UNWRAPPING_KEY_HANDLE_INVALID:  exp_ckr_other
	|CKR_UNWRAPPING_KEY_SIZE_RANGE:  exp_ckr_other
	|CKR_UNWRAPPING_KEY_TYPE_INCONSISTENT:  exp_ckr_other
	|CKR_USER_ALREADY_LOGGED_IN: exp_ckr_other
	|CKR_USER_ANOTHER_ALREADY_LOGGED_IN: exp_ckr_other
	|CKR_USER_NOT_LOGGED_IN: exp_ckr_other
	|CKR_USER_PIN_NOT_INITIALIZED: exp_ckr_other
	|CKR_USER_TOO_MANY_TYPES: exp_ckr_other
	|CKR_USER_TYPE_INVALID: exp_ckr_other
	|CKR_WRAPPED_KEY_INVALID: exp_ckr_other
	|CKR_WRAPPED_KEY_LEN_RANGE: exp_ckr_other
	|CKR_WRAPPING_KEY_HANDLE_INVALID: exp_ckr_other
	|CKR_WRAPPING_KEY_SIZE_RANGE:  exp_ckr_other
	|CKR_WRAPPING_KEY_TYPE_INCONSISTENT:  exp_ckr_other



type exception_t = 
	| G: exp: exp_ckr_general -> exception_t
	| S: exp: exp_ckr_session -> exception_t
	| T: exp: exp_ckr_token -> exception_t
	| C: exp: exp_ckr_callback -> exception_t
	| M: exp: exp_ckr_mutex -> exception_t
	| O: exp: exp_ckr_other -> exception_t
	| TestExc: exception_t 


type result 'a = either 'a exception_t

val resultLeft: exc: result 'a {Inl? exc} -> Tot 'a
let resultLeft exc = 
	match  exc with
	| Inl a -> a

val resultRight: exc: result 'a {Inr? exc} -> Tot exception_t
let resultRight exc = 
	match exc with 
	|Inr a -> a

val resultIsOk : exc: result 'a -> Tot bool
let resultIsOk exc = 
	match exc with
	| Inl _ -> true
	| _ -> false

(*At least one of them should be true *)
val expectionChoose:  exception1: result 'a ->exception2: result 'b-> Tot exception_t

let expectionChoose e1 e2 = 
    if resultIsOk e1 then 
      resultRight e2 
    else 
      resultRight e1  

(* ToChange *)
val castExpectionToRV: exc: result 'a -> Tot _CK_RV

let castExpectionToRV exc = 
	if resultIsOk exc then 0ul
	else 1ul 