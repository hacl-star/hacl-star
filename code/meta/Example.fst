module Example

#set-options "--print_bound_var_types"

%splice[] (MetaInterface.specialize [ `Client.times_sixteen; `Client.times_sixteen' ])

