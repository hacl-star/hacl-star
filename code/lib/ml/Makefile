FSTAR_HOME?=../../../dependencies/FStar

FSTAR_FILES=$(addprefix $(FSTAR_HOME)/ulib/ml/, prims.cmx FStar_Mul.cmx FStar_Float.cmx FStar_Char.cmx \
      FStar_Int8.cmx FStar_UInt8.cmx FStar_Int16.cmx FStar_UInt16.cmx \
      FStar_Int32.cmx FStar_UInt32.cmx FStar_Int64.cmx FStar_UInt64.cmx FStar_UInt128.cmx \
      FStar_Int_Cast.cmx \
      FStar_BaseTypes.cmx \
      FStar_IO.cmx FStar_Heap.cmx FStar_List_Tot_Base.cmx FStar_List.cmx \
      FStar_Option.cmx FStar_String.cmx FStar_Set.cmx \
      FStar_Buffer.cmx FStar_CommonST.cmx extracted/FStar_TSet.cmx extracted/FStar_Map.cmx extracted/FStar_HyperHeap.cmx extracted/FStar_HyperStack.cmx hyperstack/FStar_ST.cmx hyperstack/FStar_All.cmx \
)

FILES=Hacl_UInt32.mli Hacl_UInt32.ml Hacl_UInt64.mli Hacl_UInt64.ml Hacl_UInt8.mli Hacl_UInt8.ml  Hacl_UInt128.mli Hacl_UInt128.ml Hacl_Cast.ml
FILESX=Hacl_UInt32.cmx Hacl_UInt64.cmx Hacl_UInt8.cmx  Hacl_UInt128.cmx Hacl_Cast.cmx

OCAMLOPT=ocamlfind opt -thread -package batteries,zarith,stdint -linkpkg -g $(INCLUDES) $(FSTAR_HOME)/ulib/ml/fstarlib.cmxa
OCAMLDEP=ocamlfind dep
OCAMLMKLIB=ocamlfind mklib

OBJS=$(FILES:.ml=.o)
CMX=$(FILES:.ml=.cmx)

FSTAR_LIB=$(FSTAR_HOME)/ulib/ml


all: hacllib.cmxa

hacllib.cmxa:
	$(MAKE) -C $(FSTAR_LIB) MEM=HST
	ocamlfind opt -thread -package batteries,zarith,stdint -linkpkg -g -w -58 -I $(FSTAR_LIB) -I $(FSTAR_LIB)/hyperstack -I $(FSTAR_LIB)/extracted $(FSTAR_LIB)/fstarlib.cmxa  -c -linkpkg $(FILES)
	ocamlopt -a $(FSTAR_FILES) $(FILESX) -o hacllib.cmxa

clean:
	$(MAKE) -C $(FSTAR_LIB) clean
	rm -f *.cmi *.cmo *.cmx *.cmxa *.o *.a *~
