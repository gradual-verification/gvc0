#include "cc0lib.h"
#include "c0rt.h"
#include "bst.verified.c0.h"

//#use <runtime>
struct _c0_OwnedFields {
  cc0_array(struct _c0_FieldArray*) _c0_contents;
  int _c0_capacity;
  int _c0_length;
  int* _c0_instanceCounter;
};
typedef struct _c0_OwnedFields _c0_OwnedFields;
struct _c0_FieldArray {
  cc0_array(bool) _c0_contents;
  int _c0_length;
  int _c0__id;
  int _c0_numAccessible;
  bool _c0_deleted;
};
typedef struct _c0_FieldArray _c0_FieldArray;
_c0_OwnedFields* _c0_initOwnedFields(int* _c0v_instanceCounter);
int _c0_addStructAcc(_c0_OwnedFields* _c0v_fields, int _c0v_numFields);
void _c0_addAcc(_c0_OwnedFields* _c0v_fields, int _c0v__id, int _c0v_numFields, int _c0v_fieldIndex);
void _c0_loseAcc(_c0_OwnedFields* _c0v_fields, int _c0v__id, int _c0v_fieldIndex);
void _c0_join(_c0_OwnedFields* _c0v_target, _c0_OwnedFields* _c0v_source);
void _c0_assertAcc(_c0_OwnedFields* _c0v_fields, int _c0v__id, int _c0v_fieldIndex, c0_string _c0v_errorMessage);
void _c0_addAccEnsureSeparate(_c0_OwnedFields* _c0v_fields, int _c0v__id, int _c0v_fieldIndex, int _c0v_numFields, c0_string _c0v_errorMessage);
_c0_FieldArray* _c0_find(_c0_OwnedFields* _c0v_fields, int _c0v__id);

//#use <conio>
extern void print(c0_string _c0v_s);
extern void println(c0_string _c0v_s);
extern void printint(int _c0v_i);
extern void printbool(bool _c0v_b);
extern void printchar(char _c0v_c);
extern void flush();
extern bool eof();
extern c0_string readline();
// end <conio>

//#use <string>
extern int string_length(c0_string _c0v_s);
extern char string_charat(c0_string _c0v_s, int _c0v_idx);
extern c0_string string_join(c0_string _c0v_a, c0_string _c0v_b);
extern c0_string string_sub(c0_string _c0v_a, int _c0v_start, int _c0v_end);
extern bool string_equal(c0_string _c0v_a, c0_string _c0v_b);
extern int string_compare(c0_string _c0v_a, c0_string _c0v_b);
extern c0_string string_fromint(int _c0v_i);
extern c0_string string_frombool(bool _c0v_b);
extern c0_string string_fromchar(char _c0v_c);
extern c0_string string_tolower(c0_string _c0v_s);
extern bool string_terminated(cc0_array(char) _c0v_A, int _c0v_n);
extern cc0_array(char) string_to_chararray(c0_string _c0v_s);
extern c0_string string_from_chararray(cc0_array(char) _c0v_A);
extern int char_ord(char _c0v_c);
extern char char_chr(int _c0v_n);
// end <string>

int _c0_GROW_CAPACITY(int _c0v_oldCapacity) {
  return ((_c0v_oldCapacity < 128) ? 128 : (_c0v_oldCapacity + 128));
}

int _c0_hash(int _c0v_index, int _c0v_arrayLength) {
  _c0v_index = (((_c0v_index >> 16) ^ _c0v_index) * 73244475);
  _c0v_index = (((_c0v_index >> 16) ^ _c0v_index) * 73244475);
  _c0v_index = ((_c0v_index >> 16) ^ _c0v_index);
  int _c0t__tmp_2 = c0_imod(_c0v_index,_c0v_arrayLength);
  return _c0t__tmp_2;
}

_c0_OwnedFields* _c0_initOwnedFields(int* _c0v_instanceCounter) {
  struct _c0_OwnedFields* _c0t__tmp_3 = cc0_alloc(_c0_OwnedFields);
  _c0_OwnedFields* _c0v_fields = _c0t__tmp_3;
  int** _c0t__tmp_4;
  _c0t__tmp_4 = &((cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_instanceCounter);
  cc0_deref(int*, _c0t__tmp_4) = _c0v_instanceCounter;
  int _c0v_oldCapacity = 0;
  int* _c0t__tmp_5;
  _c0t__tmp_5 = &((cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity);
  int _c0t__tmp_6 = _c0_GROW_CAPACITY(_c0v_oldCapacity);
  cc0_deref(int, _c0t__tmp_5) = _c0t__tmp_6;
  cc0_array(struct _c0_FieldArray*)* _c0t__tmp_7;
  _c0t__tmp_7 = &((cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents);
  int _c0t__tmp_8 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity;
  cc0_array(struct _c0_FieldArray*) _c0t__tmp_9 = cc0_alloc_array(_c0_FieldArray*,_c0t__tmp_8);
  cc0_deref(cc0_array(struct _c0_FieldArray*), _c0t__tmp_7) = _c0t__tmp_9;
  {
    int _c0v_i = 0;
    while (true) {
      int _c0t__tmp_10 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity;
      if ((_c0v_i < _c0t__tmp_10)) {
      } else {
        break;
      }
      {
        cc0_array(struct _c0_FieldArray*) _c0t__tmp_11 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
        struct _c0_FieldArray** _c0t__tmp_12;
        _c0t__tmp_12 = &(cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_11,_c0v_i));
        cc0_deref(struct _c0_FieldArray*, _c0t__tmp_12) = NULL;
      }
      _c0v_i += 1;
    }
  }
  return _c0v_fields;
}

void _c0_grow(_c0_OwnedFields* _c0v_fields) {
  int _c0t__tmp_13 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity;
  int _c0v_oldCapacity = _c0t__tmp_13;
  int* _c0t__tmp_14;
  _c0t__tmp_14 = &((cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity);
  int _c0t__tmp_15 = _c0_GROW_CAPACITY(_c0v_oldCapacity);
  cc0_deref(int, _c0t__tmp_14) = _c0t__tmp_15;
  int _c0t__tmp_16 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity;
  cc0_array(struct _c0_FieldArray*) _c0t__tmp_17 = cc0_alloc_array(_c0_FieldArray*,_c0t__tmp_16);
  cc0_array(_c0_FieldArray*) _c0v_newContents = _c0t__tmp_17;
  {
    int _c0v_i = 0;
    while ((_c0v_i < _c0v_oldCapacity)) {
      {
        bool _c0t__tmp_23;
        cc0_array(struct _c0_FieldArray*) _c0t__tmp_18 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
        struct _c0_FieldArray* _c0t__tmp_19 = cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_18,_c0v_i);
        if ((_c0t__tmp_19 != NULL)) {
          cc0_array(struct _c0_FieldArray*) _c0t__tmp_20 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
          struct _c0_FieldArray* _c0t__tmp_21 = cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_20,_c0v_i);
          bool _c0t__tmp_22 = (cc0_deref(struct _c0_FieldArray, _c0t__tmp_21))._c0_deleted;
          _c0t__tmp_23 = !(_c0t__tmp_22);
        } else {
          _c0t__tmp_23 = false;
        }
        if (_c0t__tmp_23) {
          cc0_array(struct _c0_FieldArray*) _c0t__tmp_24 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
          struct _c0_FieldArray* _c0t__tmp_25 = cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_24,_c0v_i);
          int _c0t__tmp_26 = (cc0_deref(struct _c0_FieldArray, _c0t__tmp_25))._c0__id;
          int _c0v__id = _c0t__tmp_26;
          int _c0t__tmp_27 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity;
          int _c0t__tmp_28 = _c0_hash(_c0v__id, _c0t__tmp_27);
          int _c0v_newIndex = _c0t__tmp_28;
          while (true) {
            struct _c0_FieldArray* _c0t__tmp_29 = cc0_array_sub(struct _c0_FieldArray*,_c0v_newContents,_c0v_newIndex);
            if ((_c0t__tmp_29 != NULL)) {
            } else {
              break;
            }
            int _c0t__tmp_30 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity;
            int _c0t__tmp_31 = c0_imod((_c0v_newIndex + 1),_c0t__tmp_30);
            _c0v_newIndex = _c0t__tmp_31;
          }
          struct _c0_FieldArray** _c0t__tmp_32;
          _c0t__tmp_32 = &(cc0_array_sub(struct _c0_FieldArray*,_c0v_newContents,_c0v_newIndex));
          cc0_array(struct _c0_FieldArray*) _c0t__tmp_33 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
          struct _c0_FieldArray* _c0t__tmp_34 = cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_33,_c0v_i);
          cc0_deref(struct _c0_FieldArray*, _c0t__tmp_32) = _c0t__tmp_34;
        }
      }
      _c0v_i += 1;
    }
  }
  cc0_array(struct _c0_FieldArray*)* _c0t__tmp_35;
  _c0t__tmp_35 = &((cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents);
  cc0_deref(cc0_array(struct _c0_FieldArray*), _c0t__tmp_35) = _c0v_newContents;
}

_c0_FieldArray* _c0_find(_c0_OwnedFields* _c0v_fields, int _c0v__id) {
  if ((_c0v__id >= 0)) {
    int _c0t__tmp_36 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity;
    int _c0t__tmp_37 = _c0_hash(_c0v__id, _c0t__tmp_36);
    int _c0v_index = _c0t__tmp_37;
    while (true) {
      cc0_array(struct _c0_FieldArray*) _c0t__tmp_38 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
      struct _c0_FieldArray* _c0t__tmp_39 = cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_38,_c0v_index);
      if ((_c0t__tmp_39 != NULL)) {
      } else {
        break;
      }
      bool _c0t__tmp_46;
      cc0_array(struct _c0_FieldArray*) _c0t__tmp_40 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
      struct _c0_FieldArray* _c0t__tmp_41 = cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_40,_c0v_index);
      bool _c0t__tmp_42 = (cc0_deref(struct _c0_FieldArray, _c0t__tmp_41))._c0_deleted;
      if (!(_c0t__tmp_42)) {
        cc0_array(struct _c0_FieldArray*) _c0t__tmp_43 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
        struct _c0_FieldArray* _c0t__tmp_44 = cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_43,_c0v_index);
        int _c0t__tmp_45 = (cc0_deref(struct _c0_FieldArray, _c0t__tmp_44))._c0__id;
        _c0t__tmp_46 = (_c0t__tmp_45 == _c0v__id);
      } else {
        _c0t__tmp_46 = false;
      }
      if (_c0t__tmp_46) {
        cc0_array(struct _c0_FieldArray*) _c0t__tmp_47 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
        struct _c0_FieldArray* _c0t__tmp_48 = cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_47,_c0v_index);
        return _c0t__tmp_48;
      } else {
        int _c0t__tmp_49 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity;
        int _c0t__tmp_50 = c0_imod((_c0v_index + 1),_c0t__tmp_49);
        _c0v_index = _c0t__tmp_50;
      }
    }
  }
  return NULL;
}

_c0_FieldArray* _c0_newFieldArray(_c0_OwnedFields* _c0v_fields, int _c0v__id, int _c0v_numFields, bool _c0v_accAll) {
  int _c0t__tmp_51 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_length;
  int _c0t__tmp_52 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity;
  if ((_c0t__tmp_51 > (_c0t__tmp_52 * (4 / 5)))) {
    _c0_grow(_c0v_fields);
  }
  int _c0t__tmp_53 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity;
  int _c0t__tmp_54 = _c0_hash(_c0v__id, _c0t__tmp_53);
  int _c0v_fieldIndex = _c0t__tmp_54;
  while (true) {
    bool _c0t__tmp_60;
    cc0_array(struct _c0_FieldArray*) _c0t__tmp_55 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
    struct _c0_FieldArray* _c0t__tmp_56 = cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_55,_c0v_fieldIndex);
    if ((_c0t__tmp_56 != NULL)) {
      cc0_array(struct _c0_FieldArray*) _c0t__tmp_57 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
      struct _c0_FieldArray* _c0t__tmp_58 = cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_57,_c0v_fieldIndex);
      bool _c0t__tmp_59 = (cc0_deref(struct _c0_FieldArray, _c0t__tmp_58))._c0_deleted;
      _c0t__tmp_60 = !(_c0t__tmp_59);
    } else {
      _c0t__tmp_60 = false;
    }
    if (_c0t__tmp_60) {
    } else {
      break;
    }
    int _c0t__tmp_61 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_capacity;
    int _c0t__tmp_62 = c0_imod((_c0v_fieldIndex + 1),_c0t__tmp_61);
    _c0v_fieldIndex = _c0t__tmp_62;
  }
  struct _c0_FieldArray* _c0t__tmp_63 = cc0_alloc(_c0_FieldArray);
  _c0_FieldArray* _c0v_array = _c0t__tmp_63;
  cc0_array(struct _c0_FieldArray*) _c0t__tmp_64 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
  struct _c0_FieldArray** _c0t__tmp_65;
  _c0t__tmp_65 = &(cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_64,_c0v_fieldIndex));
  cc0_deref(struct _c0_FieldArray*, _c0t__tmp_65) = _c0v_array;
  (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_length += 1;
  cc0_array(bool)* _c0t__tmp_66;
  _c0t__tmp_66 = &((cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_contents);
  cc0_array(bool) _c0t__tmp_67 = cc0_alloc_array(bool,_c0v_numFields);
  cc0_deref(cc0_array(bool), _c0t__tmp_66) = _c0t__tmp_67;
  int* _c0t__tmp_68;
  _c0t__tmp_68 = &((cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_length);
  cc0_deref(int, _c0t__tmp_68) = _c0v_numFields;
  int* _c0t__tmp_69;
  _c0t__tmp_69 = &((cc0_deref(struct _c0_FieldArray, _c0v_array))._c0__id);
  cc0_deref(int, _c0t__tmp_69) = _c0v__id;
  bool* _c0t__tmp_70;
  _c0t__tmp_70 = &((cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_deleted);
  cc0_deref(bool, _c0t__tmp_70) = false;
  {
    int _c0v_i = 0;
    while (true) {
      int _c0t__tmp_71 = (cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_length;
      if ((_c0v_i < _c0t__tmp_71)) {
      } else {
        break;
      }
      {
        cc0_array(bool) _c0t__tmp_72 = (cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_contents;
        bool* _c0t__tmp_73;
        _c0t__tmp_73 = &(cc0_array_sub(bool,_c0t__tmp_72,_c0v_i));
        cc0_deref(bool, _c0t__tmp_73) = _c0v_accAll;
      }
      _c0v_i += 1;
    }
  }
  if (_c0v_accAll) {
    int* _c0t__tmp_74;
    _c0t__tmp_74 = &((cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_numAccessible);
    int _c0t__tmp_75 = (cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_length;
    cc0_deref(int, _c0t__tmp_74) = _c0t__tmp_75;
  } else {
    int* _c0t__tmp_76;
    _c0t__tmp_76 = &((cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_numAccessible);
    cc0_deref(int, _c0t__tmp_76) = 0;
  }
  cc0_array(struct _c0_FieldArray*) _c0t__tmp_77 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_contents;
  struct _c0_FieldArray* _c0t__tmp_78 = cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_77,_c0v_fieldIndex);
  return _c0t__tmp_78;
}

int _c0_addStructAcc(_c0_OwnedFields* _c0v_fields, int _c0v_numFields) {
  int* _c0t__tmp_79 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_instanceCounter;
  int _c0t__tmp_80 = cc0_deref(int, _c0t__tmp_79);
  _c0_newFieldArray(_c0v_fields, _c0t__tmp_80, _c0v_numFields, true);
  int* _c0t__tmp_81 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_instanceCounter;
  cc0_deref(int, _c0t__tmp_81) += 1;
  int* _c0t__tmp_82 = (cc0_deref(struct _c0_OwnedFields, _c0v_fields))._c0_instanceCounter;
  int _c0t__tmp_83 = cc0_deref(int, _c0t__tmp_82);
  return (_c0t__tmp_83 - 1);
}

void _c0_addAcc(_c0_OwnedFields* _c0v_fields, int _c0v__id, int _c0v_numFields, int _c0v_fieldIndex) {
  struct _c0_FieldArray* _c0t__tmp_84 = _c0_find(_c0v_fields, _c0v__id);
  _c0_FieldArray* _c0v_array = _c0t__tmp_84;
  if ((_c0v_array != NULL)) {
    cc0_array(bool) _c0t__tmp_85 = (cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_contents;
    bool _c0t__tmp_86 = cc0_array_sub(bool,_c0t__tmp_85,_c0v_fieldIndex);
    if (!(_c0t__tmp_86)) {
      (cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_numAccessible += 1;
      cc0_array(bool) _c0t__tmp_87 = (cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_contents;
      bool* _c0t__tmp_88;
      _c0t__tmp_88 = &(cc0_array_sub(bool,_c0t__tmp_87,_c0v_fieldIndex));
      cc0_deref(bool, _c0t__tmp_88) = true;
    }
  } else {
    struct _c0_FieldArray* _c0t__tmp_89 = _c0_newFieldArray(_c0v_fields, _c0v__id, _c0v_numFields, false);
    _c0v_array = _c0t__tmp_89;
    cc0_array(bool) _c0t__tmp_90 = (cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_contents;
    bool* _c0t__tmp_91;
    _c0t__tmp_91 = &(cc0_array_sub(bool,_c0t__tmp_90,_c0v_fieldIndex));
    cc0_deref(bool, _c0t__tmp_91) = true;
    (cc0_deref(struct _c0_FieldArray, _c0v_array))._c0_numAccessible += 1;
  }
}

void _c0_assertAcc(_c0_OwnedFields* _c0v_fields, int _c0v__id, int _c0v_fieldIndex, c0_string _c0v_errorMessage) {
  struct _c0_FieldArray* _c0t__tmp_92 = _c0_find(_c0v_fields, _c0v__id);
  _c0_FieldArray* _c0v_toCheck = _c0t__tmp_92;
  bool _c0t__tmp_95;
  if ((_c0v_toCheck == NULL)) {
    _c0t__tmp_95 = true;
  } else {
    cc0_array(bool) _c0t__tmp_93 = (cc0_deref(struct _c0_FieldArray, _c0v_toCheck))._c0_contents;
    bool _c0t__tmp_94 = cc0_array_sub(bool,_c0t__tmp_93,_c0v_fieldIndex);
    _c0t__tmp_95 = !(_c0t__tmp_94);
  }
  if (_c0t__tmp_95) {
    c0_error(_c0v_errorMessage);
    exit(EXIT_FAILURE);
  }
}

void _c0_addAccEnsureSeparate(_c0_OwnedFields* _c0v_fields, int _c0v__id, int _c0v_fieldIndex, int _c0v_numFields, c0_string _c0v_errorMessage) {
  struct _c0_FieldArray* _c0t__tmp_96 = _c0_find(_c0v_fields, _c0v__id);
  _c0_FieldArray* _c0v_toCheck = _c0t__tmp_96;
  if ((_c0v_toCheck == NULL)) {
    struct _c0_FieldArray* _c0t__tmp_97 = _c0_newFieldArray(_c0v_fields, _c0v__id, _c0v_numFields, false);
    _c0v_toCheck = _c0t__tmp_97;
  } else {
    cc0_array(bool) _c0t__tmp_98 = (cc0_deref(struct _c0_FieldArray, _c0v_toCheck))._c0_contents;
    bool _c0t__tmp_99 = cc0_array_sub(bool,_c0t__tmp_98,_c0v_fieldIndex);
    if (_c0t__tmp_99) {
      c0_error(_c0v_errorMessage);
      exit(EXIT_FAILURE);
    }
  }
  cc0_array(bool) _c0t__tmp_100 = (cc0_deref(struct _c0_FieldArray, _c0v_toCheck))._c0_contents;
  bool* _c0t__tmp_101;
  _c0t__tmp_101 = &(cc0_array_sub(bool,_c0t__tmp_100,_c0v_fieldIndex));
  cc0_deref(bool, _c0t__tmp_101) = true;
  (cc0_deref(struct _c0_FieldArray, _c0v_toCheck))._c0_numAccessible += 1;
}

void _c0_loseAcc(_c0_OwnedFields* _c0v_fields, int _c0v__id, int _c0v_fieldIndex) {
  struct _c0_FieldArray* _c0t__tmp_102 = _c0_find(_c0v_fields, _c0v__id);
  _c0_FieldArray* _c0v_toLose = _c0t__tmp_102;
  if ((_c0v_toLose != NULL)) {
    int _c0t__tmp_103 = (cc0_deref(struct _c0_FieldArray, _c0v_toLose))._c0_length;
    if ((_c0v_fieldIndex >= _c0t__tmp_103)) {
      c0_error(c0_string_fromliteral("[INTERNAL] Field index exceeds maximum for the given struct.\n"));
      exit(EXIT_FAILURE);
    } else {
      cc0_array(bool) _c0t__tmp_104 = (cc0_deref(struct _c0_FieldArray, _c0v_toLose))._c0_contents;
      bool _c0t__tmp_105 = cc0_array_sub(bool,_c0t__tmp_104,_c0v_fieldIndex);
      if (_c0t__tmp_105) {
        cc0_array(bool) _c0t__tmp_106 = (cc0_deref(struct _c0_FieldArray, _c0v_toLose))._c0_contents;
        bool* _c0t__tmp_107;
        _c0t__tmp_107 = &(cc0_array_sub(bool,_c0t__tmp_106,_c0v_fieldIndex));
        cc0_deref(bool, _c0t__tmp_107) = false;
        (cc0_deref(struct _c0_FieldArray, _c0v_toLose))._c0_numAccessible -= 1;
      }
    }
    int _c0t__tmp_108 = (cc0_deref(struct _c0_FieldArray, _c0v_toLose))._c0_numAccessible;
    if ((_c0t__tmp_108 == 0)) {
      bool* _c0t__tmp_109;
      _c0t__tmp_109 = &((cc0_deref(struct _c0_FieldArray, _c0v_toLose))._c0_deleted);
      cc0_deref(bool, _c0t__tmp_109) = true;
    }
  }
}

void _c0_join(_c0_OwnedFields* _c0v_target, _c0_OwnedFields* _c0v_source) {
  if (((_c0v_source != NULL) && (_c0v_target != NULL))) {
    int _c0v_i = 0;
    while (true) {
      int _c0t__tmp_111 = (cc0_deref(struct _c0_OwnedFields, _c0v_source))._c0_capacity;
      if ((_c0v_i < _c0t__tmp_111)) {
      } else {
        break;
      }
      {
        cc0_array(struct _c0_FieldArray*) _c0t__tmp_112 = (cc0_deref(struct _c0_OwnedFields, _c0v_source))._c0_contents;
        struct _c0_FieldArray* _c0t__tmp_113 = cc0_array_sub(struct _c0_FieldArray*,_c0t__tmp_112,_c0v_i);
        _c0_FieldArray* _c0v_currFields = _c0t__tmp_113;
        if ((_c0v_currFields != NULL)) {
          int _c0v_j = 0;
          while (true) {
            int _c0t__tmp_114 = (cc0_deref(struct _c0_FieldArray, _c0v_currFields))._c0_length;
            if ((_c0v_j < _c0t__tmp_114)) {
            } else {
              break;
            }
            {
              int _c0t__tmp_115 = (cc0_deref(struct _c0_FieldArray, _c0v_currFields))._c0__id;
              int _c0t__tmp_116 = (cc0_deref(struct _c0_FieldArray, _c0v_currFields))._c0_length;
              _c0_addAcc(_c0v_target, _c0t__tmp_115, _c0t__tmp_116, _c0v_j);
            }
            _c0v_j += 1;
          }
        }
      }
      _c0v_i += 1;
    }
  }
}
// end <runtime>

//#use <stress>
int _c0_mod(int _c0v_r, int _c0v_l);
int _c0_rand(int _c0v_prev);
int _c0_readStress();

//#use <util>
int _c0_int_size();
int _c0_int_max();
int _c0_int_min();
int _c0_abs(int _c0v_x);
int _c0_max(int _c0v_x, int _c0v_y);
int _c0_min(int _c0v_x, int _c0v_y);
c0_string _c0_int2hex(int _c0v_x);

//#use <string>
// end <string>

int _c0_int_size() {
  return 4;
}

int _c0_int_max() {
  return 2147483647;
}

int _c0_int_min() {
  return (-2147483647-1);
}

int _c0_max(int _c0v_x, int _c0v_y) {
  return ((_c0v_x > _c0v_y) ? _c0v_x : _c0v_y);
}

int _c0_min(int _c0v_x, int _c0v_y) {
  return ((_c0v_x > _c0v_y) ? _c0v_y : _c0v_x);
}

int _c0_abs(int _c0v_x) {
  return ((_c0v_x < 0) ? -(_c0v_x) : _c0v_x);
}

char _c0_hexdig2char(int _c0v_d) {
  if (((0 <= _c0v_d) && (_c0v_d < 10))) {
    int _c0t__tmp_121 = char_ord('0');
    char _c0t__tmp_122 = char_chr((_c0t__tmp_121 + _c0v_d));
    return _c0t__tmp_122;
  } else {
    if (((10 <= _c0v_d) && (_c0v_d < 16))) {
      int _c0t__tmp_124 = char_ord('A');
      char _c0t__tmp_125 = char_chr((_c0t__tmp_124 + (_c0v_d - 10)));
      return _c0t__tmp_125;
    } else {
      return '\?';
    }
  }
}

c0_string _c0_int2hex(int _c0v_x) {
  int _c0t__tmp_126 = _c0_int_size();
  int _c0v_digits = (2 * _c0t__tmp_126);
  cc0_array(char) _c0t__tmp_127 = cc0_alloc_array(char,(_c0v_digits + 1));
  cc0_array(char) _c0v_s = _c0t__tmp_127;
  char* _c0t__tmp_128;
  _c0t__tmp_128 = &(cc0_array_sub(char,_c0v_s,_c0v_digits));
  cc0_deref(char, _c0t__tmp_128) = '\000';
  {
    int _c0v_i = 0;
    while ((_c0v_i < _c0v_digits)) {
      {
        char* _c0t__tmp_129;
        _c0t__tmp_129 = &(cc0_array_sub(char,_c0v_s,((_c0v_digits - _c0v_i) - 1)));
        char _c0t__tmp_130 = _c0_hexdig2char((_c0v_x & 15));
        cc0_deref(char, _c0t__tmp_129) = _c0t__tmp_130;
        _c0v_x = (_c0v_x >> 4);
      }
      _c0v_i += 1;
    }
  }
  c0_string _c0t__tmp_131 = string_from_chararray(_c0v_s);
  return _c0t__tmp_131;
}
// end <util>

int _c0_mod(int _c0v_r, int _c0v_l) {
  int _c0t__tmp_132 = c0_imod(_c0v_r,_c0v_l);
  int _c0t__tmp_133 = _c0_abs(_c0t__tmp_132);
  return _c0t__tmp_133;
}

int _c0_rand(int _c0v_prev) {
  int _c0v_unbounded = ((1103515245 * _c0v_prev) + 12345);
  int _c0t__tmp_134 = _c0_mod(_c0v_unbounded, (-2147483647-1));
  return _c0t__tmp_134;
}
// end <stress>
struct _c0_Node;
struct _c0_Node {
  int _c0_val;
  struct _c0_Node* _c0_left;
  struct _c0_Node* _c0_right;
  int _c0__id;
};
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_bst(struct _c0_Node* _c0v_root, int _c0v_min, int _c0v_max, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_tree(struct _c0_Node* _c0v_root, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_bst(struct _c0_Node* _c0v_root, int _c0v_min, int _c0v_max, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_OwnedFields;
struct _c0_Node* _c0_create_tree(int _c0v_val, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_OwnedFields;
struct _c0_Node* _c0_create_tree_helper(int _c0v_val, int _c0v_min, int _c0v_max, struct _c0_OwnedFields* _c0v__ownedFields);
int _c0_main();
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sep_bst(struct _c0_Node* _c0v_root, int _c0v_min, int _c0v_max, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_OwnedFields;
struct _c0_Node* _c0_tree_add(struct _c0_Node* _c0v_root, int _c0v_x, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_OwnedFields;
struct _c0_Node* _c0_tree_add_helper(struct _c0_Node* _c0v_root, int _c0v_x, int _c0v_min, int _c0v_max, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
bool _c0_tree_contains(struct _c0_Node* _c0v_root, int _c0v_x, int* _c0v__instanceCounter);
struct _c0_Node;
bool _c0_tree_contains_helper(struct _c0_Node* _c0v_root, int _c0v_x, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);
struct _c0_Node;
void _c0_tree_main_lemma(struct _c0_Node* _c0v_root, int _c0v_x, int* _c0v__instanceCounter);
struct _c0_Node;
void _c0_tree_main_lemma_bst(struct _c0_Node* _c0v_root, int _c0v_x, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);
struct _c0_Node;
int _c0_tree_max(struct _c0_Node* _c0v_root, int* _c0v__instanceCounter);
struct _c0_Node;
int _c0_tree_max_helper(struct _c0_Node* _c0v_root, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);
struct _c0_Node;
void _c0_tree_max_lemma(struct _c0_Node* _c0v_root, int _c0v_newMax, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);
struct _c0_Node;
int _c0_tree_min(struct _c0_Node* _c0v_root, int* _c0v__instanceCounter);
struct _c0_Node;
int _c0_tree_min_helper(struct _c0_Node* _c0v_root, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);
struct _c0_Node;
void _c0_tree_min_lemma(struct _c0_Node* _c0v_root, int _c0v_newMin, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);
struct _c0_Node;
struct _c0_Node* _c0_tree_remove(struct _c0_Node* _c0v_root, int _c0v_x, int* _c0v__instanceCounter);
struct _c0_Node;
struct _c0_Node* _c0_tree_remove_helper(struct _c0_Node* _c0v_root, int _c0v_x, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);
struct _c0_Node;
void _c0_tree_remove_lemma(struct _c0_Node* _c0v_root, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);
struct _c0_Node;
void _c0_tree_remove_lemma_left(struct _c0_Node* _c0v_l, int _c0v_x, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);
struct _c0_Node;
void _c0_tree_remove_lemma_left2(struct _c0_Node* _c0v_l, int _c0v_newX, int _c0v_x, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);
struct _c0_Node;
void _c0_tree_remove_lemma_max(struct _c0_Node* _c0v_root, int _c0v_x, int _c0v_newMax, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);
struct _c0_Node;
void _c0_tree_remove_lemma_min(struct _c0_Node* _c0v_root, int _c0v_x, int _c0v_newMin, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);
struct _c0_Node;
void _c0_tree_remove_lemma_right(struct _c0_Node* _c0v_r, int _c0v_x, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter);

struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_bst(struct _c0_Node* _c0v_root, int _c0v_min, int _c0v_max, struct _c0_OwnedFields* _c0v__ownedFields) {
  if (!((_c0v_root == NULL))) {
    int _c0t__tmp_135 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
    _c0_addAcc(_c0v__ownedFields, _c0t__tmp_135, 4, 1);
    int _c0t__tmp_136 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
    _c0_addAcc(_c0v__ownedFields, _c0t__tmp_136, 4, 2);
    int _c0t__tmp_137 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
    _c0_addAcc(_c0v__ownedFields, _c0t__tmp_137, 4, 0);
    struct _c0_Node* _c0t__tmp_138 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
    int _c0t__tmp_139 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_add_bst(_c0t__tmp_138, _c0v_min, (_c0t__tmp_139 - 1), _c0v__ownedFields);
    struct _c0_Node* _c0t__tmp_140 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_right;
    int _c0t__tmp_141 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_add_bst(_c0t__tmp_140, (_c0t__tmp_141 + 1), _c0v_max, _c0v__ownedFields);
  }
}

struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_tree(struct _c0_Node* _c0v_root, struct _c0_OwnedFields* _c0v__ownedFields) {
  _c0_add_bst(_c0v_root, -(2147483647), 2147483647, _c0v__ownedFields);
}

struct _c0_Node;
struct _c0_OwnedFields;
void _c0_bst(struct _c0_Node* _c0v_root, int _c0v_min, int _c0v_max, struct _c0_OwnedFields* _c0v__ownedFields) {
  if ((_c0v_root == NULL)) {
    cc0_assert(true, c0_string_fromliteral("src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 62.5-62.18: assert failed"));
  } else {
    int _c0t__tmp_143;
    if ((_c0v_root != NULL)) {
      int _c0t__tmp_142 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
      _c0t__tmp_143 = _c0t__tmp_142;
    } else {
      _c0t__tmp_143 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_143, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.left"));
    int _c0t__tmp_145;
    if ((_c0v_root != NULL)) {
      int _c0t__tmp_144 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
      _c0t__tmp_145 = _c0t__tmp_144;
    } else {
      _c0t__tmp_145 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_145, 2, c0_string_fromliteral("Field access runtime check failed for struct Node.right"));
    int _c0t__tmp_147;
    if ((_c0v_root != NULL)) {
      int _c0t__tmp_146 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
      _c0t__tmp_147 = _c0t__tmp_146;
    } else {
      _c0t__tmp_147 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_147, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
    int _c0t__tmp_148 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    cc0_assert((_c0t__tmp_148 >= _c0v_min), c0_string_fromliteral("src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 69.5-69.30: assert failed"));
    int _c0t__tmp_149 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    cc0_assert((_c0t__tmp_149 <= _c0v_max), c0_string_fromliteral("src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 70.5-70.30: assert failed"));
    struct _c0_Node* _c0t__tmp_150 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
    int _c0t__tmp_151 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_bst(_c0t__tmp_150, _c0v_min, (_c0t__tmp_151 - 1), _c0v__ownedFields);
    struct _c0_Node* _c0t__tmp_152 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_right;
    int _c0t__tmp_153 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_bst(_c0t__tmp_152, (_c0t__tmp_153 + 1), _c0v_max, _c0v__ownedFields);
  }
}

struct _c0_OwnedFields;
struct _c0_Node* _c0_create_tree(int _c0v_val, struct _c0_OwnedFields* _c0v__ownedFields) {
  struct _c0_Node* _c0v_res = NULL;
  struct _c0_Node* _c0t__tmp_154 = _c0_create_tree_helper(_c0v_val, -(2147483647), 2147483647, _c0v__ownedFields);
  _c0v_res = _c0t__tmp_154;
  _c0_bst(_c0v_res, -(2147483647), 2147483647, _c0v__ownedFields);
  return _c0v_res;
}

struct _c0_OwnedFields;
struct _c0_Node* _c0_create_tree_helper(int _c0v_val, int _c0v_min, int _c0v_max, struct _c0_OwnedFields* _c0v__ownedFields) {
  struct _c0_Node* _c0v_root = NULL;
  struct _c0_Node* _c0t__tmp_155 = cc0_alloc(struct _c0_Node);
  _c0v_root = _c0t__tmp_155;
  int* _c0t__tmp_156;
  _c0t__tmp_156 = &((cc0_deref(struct _c0_Node, _c0v_root))._c0__id);
  int _c0t__tmp_157 = _c0_addStructAcc(_c0v__ownedFields, 4);
  cc0_deref(int, _c0t__tmp_156) = _c0t__tmp_157;
  int* _c0t__tmp_158;
  _c0t__tmp_158 = &((cc0_deref(struct _c0_Node, _c0v_root))._c0_val);
  cc0_deref(int, _c0t__tmp_158) = _c0v_val;
  struct _c0_Node** _c0t__tmp_159;
  _c0t__tmp_159 = &((cc0_deref(struct _c0_Node, _c0v_root))._c0_left);
  cc0_deref(struct _c0_Node*, _c0t__tmp_159) = NULL;
  struct _c0_Node** _c0t__tmp_160;
  _c0t__tmp_160 = &((cc0_deref(struct _c0_Node, _c0v_root))._c0_right);
  cc0_deref(struct _c0_Node*, _c0t__tmp_160) = NULL;
  return _c0v_root;
}

int _c0_main() {
  int _c0v_stress = 0;
  int _c0v_seed = 0;
  int _c0v_stressCaptured = 0;
  struct _c0_Node* _c0v_t1 = NULL;
  int _c0v_i = 0;
  int _c0v_j = 0;
  int _c0v_r = 0;
  int _c0v_toAdd = 0;
  bool _c0v_test = false;
  int _c0v_r1 = 0;
  int _c0v_toRemove = 0;
  bool _c0v_test1 = false;
  struct _c0_Node* _c0v_t11 = NULL;
  struct _c0_Node* _c0v_t12 = NULL;
  int* _c0v__instanceCounter = NULL;
  struct _c0_OwnedFields* _c0v__tempFields = NULL;
  struct _c0_OwnedFields* _c0v__tempFields1 = NULL;
  int* _c0t__tmp_161 = cc0_alloc(int);
  _c0v__instanceCounter = _c0t__tmp_161;
  _c0v_stress = 0;
  _c0v_seed = 1;
  _c0v_stressCaptured = _c0v_stress;
  if ((((_c0v_stressCaptured / 2) * 2) != _c0v_stressCaptured)) {
    _c0v_stressCaptured = (_c0v_stressCaptured + 1);
  }
  struct _c0_OwnedFields* _c0t__tmp_162 = _c0_initOwnedFields(_c0v__instanceCounter);
  _c0v__tempFields = _c0t__tmp_162;
  struct _c0_Node* _c0t__tmp_163 = _c0_create_tree(_c0v_stressCaptured, _c0v__tempFields);
  _c0v_t1 = _c0t__tmp_163;
  _c0v_i = 0;
  while (((0 <= _c0v_i) && (_c0v_i < _c0v_stressCaptured))) {
    int _c0t__tmp_165 = _c0_rand(_c0v_seed);
    _c0v_r = _c0t__tmp_165;
    _c0v_seed = _c0v_r;
    int _c0t__tmp_166 = _c0_mod(_c0v_r, (2 * _c0v_stressCaptured));
    _c0v_toAdd = _c0t__tmp_166;
    struct _c0_OwnedFields* _c0t__tmp_167 = _c0_initOwnedFields(_c0v__instanceCounter);
    _c0v__tempFields1 = _c0t__tmp_167;
    struct _c0_Node* _c0t__tmp_168 = _c0_tree_add(_c0v_t1, _c0v_toAdd, _c0v__tempFields1);
    _c0v_t11 = _c0t__tmp_168;
    bool _c0t__tmp_169 = _c0_tree_contains(_c0v_t11, _c0v_toAdd, _c0v__instanceCounter);
    _c0v_test = _c0t__tmp_169;
    cc0_assert(_c0v_test, c0_string_fromliteral("src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 133.5-133.18: assert failed"));
    _c0v_i = (_c0v_i + 1);
    _c0v_t1 = _c0v_t11;
  }
  _c0v_j = 0;
  while ((_c0v_j < _c0v_stressCaptured)) {
    int _c0t__tmp_170 = _c0_rand(_c0v_seed);
    _c0v_r1 = _c0t__tmp_170;
    _c0v_seed = _c0v_r1;
    int _c0t__tmp_171 = _c0_mod(_c0v_r1, (2 * _c0v_stressCaptured));
    _c0v_toRemove = _c0t__tmp_171;
    struct _c0_Node* _c0t__tmp_172 = _c0_tree_remove(_c0v_t1, _c0v_toRemove, _c0v__instanceCounter);
    _c0v_t12 = _c0t__tmp_172;
    _c0_tree_main_lemma(_c0v_t12, _c0v_toRemove, _c0v__instanceCounter);
    bool _c0t__tmp_173 = _c0_tree_contains(_c0v_t12, _c0v_toRemove, _c0v__instanceCounter);
    _c0v_test1 = _c0t__tmp_173;
    cc0_assert(!(_c0v_test1), c0_string_fromliteral("src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 146.5-146.20: assert failed"));
    _c0v_j = (_c0v_j + 1);
    _c0v_t1 = _c0v_t12;
  }
  return 0;
}

struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sep_bst(struct _c0_Node* _c0v_root, int _c0v_min, int _c0v_max, struct _c0_OwnedFields* _c0v__ownedFields) {
  if (!((_c0v_root == NULL))) {
    int _c0t__tmp_175;
    if ((_c0v_root != NULL)) {
      int _c0t__tmp_174 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
      _c0t__tmp_175 = _c0t__tmp_174;
    } else {
      _c0t__tmp_175 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__ownedFields, _c0t__tmp_175, 1, 4, c0_string_fromliteral("Overlapping field permissions for struct Node.left"));
    int _c0t__tmp_177;
    if ((_c0v_root != NULL)) {
      int _c0t__tmp_176 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
      _c0t__tmp_177 = _c0t__tmp_176;
    } else {
      _c0t__tmp_177 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__ownedFields, _c0t__tmp_177, 2, 4, c0_string_fromliteral("Overlapping field permissions for struct Node.right"));
    int _c0t__tmp_179;
    if ((_c0v_root != NULL)) {
      int _c0t__tmp_178 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
      _c0t__tmp_179 = _c0t__tmp_178;
    } else {
      _c0t__tmp_179 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__ownedFields, _c0t__tmp_179, 0, 4, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
    struct _c0_Node* _c0t__tmp_180 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
    int _c0t__tmp_181 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_sep_bst(_c0t__tmp_180, _c0v_min, (_c0t__tmp_181 - 1), _c0v__ownedFields);
    struct _c0_Node* _c0t__tmp_182 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_right;
    int _c0t__tmp_183 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_sep_bst(_c0t__tmp_182, (_c0t__tmp_183 + 1), _c0v_max, _c0v__ownedFields);
  }
}

struct _c0_Node;
struct _c0_OwnedFields;
struct _c0_Node* _c0_tree_add(struct _c0_Node* _c0v_root, int _c0v_x, struct _c0_OwnedFields* _c0v__ownedFields) {
  struct _c0_Node* _c0v_res = NULL;
  _c0_add_tree(_c0v_root, _c0v__ownedFields);
  struct _c0_Node* _c0t__tmp_184 = _c0_tree_add_helper(_c0v_root, _c0v_x, -(2147483647), 2147483647, _c0v__ownedFields);
  _c0v_res = _c0t__tmp_184;
  return _c0v_res;
}

struct _c0_Node;
struct _c0_OwnedFields;
struct _c0_Node* _c0_tree_add_helper(struct _c0_Node* _c0v_root, int _c0v_x, int _c0v_min, int _c0v_max, struct _c0_OwnedFields* _c0v__ownedFields) {
  struct _c0_Node* _c0v__ = NULL;
  int _c0v_v = 0;
  struct _c0_Node* _c0v_l = NULL;
  struct _c0_Node* _c0v_r = NULL;
  struct _c0_Node* _c0v__1 = NULL;
  struct _c0_Node* _c0v__2 = NULL;
  struct _c0_Node* _c0v__3 = NULL;
  struct _c0_Node* _c0v__4 = NULL;
  bool _c0v__cond_1 = false;
  bool _c0v__cond_2 = false;
  bool _c0v__cond_3 = false;
  bool _c0v__cond_4 = false;
  bool _c0v__cond_5 = false;
  bool _c0v__cond_6 = false;
  struct _c0_OwnedFields* _c0v__tempFields = NULL;
  struct _c0_OwnedFields* _c0v__tempFields1 = NULL;
  _c0v__cond_1 = (_c0v_root == NULL);
  _c0v__cond_2 = (_c0v_root == NULL);
  if ((_c0v_root == NULL)) {
    struct _c0_Node* _c0t__tmp_185 = _c0_create_tree_helper(_c0v_x, _c0v_min, _c0v_max, _c0v__ownedFields);
    _c0v__ = _c0t__tmp_185;
    int* _c0t__tmp_186 = (cc0_deref(struct _c0_OwnedFields, _c0v__ownedFields))._c0_instanceCounter;
    struct _c0_OwnedFields* _c0t__tmp_187 = _c0_initOwnedFields(_c0t__tmp_186);
    _c0v__tempFields = _c0t__tmp_187;
    if ((_c0v__cond_1 && _c0v__cond_2)) {
      _c0_bst(_c0v__, _c0v_min, _c0v_max, _c0v__ownedFields);
    }
    _c0_sep_bst(_c0v__, _c0v_min, _c0v_max, _c0v__tempFields);
    return _c0v__;
  } else {
    int _c0t__tmp_189 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0v_v = _c0t__tmp_189;
    struct _c0_Node* _c0t__tmp_190 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
    _c0v_l = _c0t__tmp_190;
    struct _c0_Node* _c0t__tmp_191 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_right;
    _c0v_r = _c0t__tmp_191;
    _c0v__cond_3 = (_c0v_x < _c0v_v);
    if ((_c0v_x < _c0v_v)) {
      _c0v__cond_4 = (_c0v_l == NULL);
      if ((_c0v_l != NULL)) {
        struct _c0_Node* _c0t__tmp_192 = _c0_tree_add_helper(_c0v_l, _c0v_x, _c0v_min, (_c0v_v - 1), _c0v__ownedFields);
        _c0v__1 = _c0t__tmp_192;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          int _c0t__tmp_197;
          if ((_c0v_root != NULL)) {
            int _c0t__tmp_196 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
            _c0t__tmp_197 = _c0t__tmp_196;
          } else {
            _c0t__tmp_197 = -(1);
          }
          _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_197, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.left"));
        }
        struct _c0_Node** _c0t__tmp_198;
        _c0t__tmp_198 = &((cc0_deref(struct _c0_Node, _c0v_root))._c0_left);
        cc0_deref(struct _c0_Node*, _c0t__tmp_198) = _c0v__1;
      } else {
        struct _c0_Node* _c0t__tmp_199 = _c0_create_tree_helper(_c0v_x, _c0v_min, (_c0v_v - 1), _c0v__ownedFields);
        _c0v__2 = _c0t__tmp_199;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4)) {
          int _c0t__tmp_204;
          if ((_c0v_root != NULL)) {
            int _c0t__tmp_203 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
            _c0t__tmp_204 = _c0t__tmp_203;
          } else {
            _c0t__tmp_204 = -(1);
          }
          _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_204, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.left"));
        }
        struct _c0_Node** _c0t__tmp_205;
        _c0t__tmp_205 = &((cc0_deref(struct _c0_Node, _c0v_root))._c0_left);
        cc0_deref(struct _c0_Node*, _c0t__tmp_205) = _c0v__2;
      }
    } else {
      _c0v__cond_5 = (_c0v_v < _c0v_x);
      if ((_c0v_v < _c0v_x)) {
        _c0v__cond_6 = (_c0v_r == NULL);
        if ((_c0v_r != NULL)) {
          struct _c0_Node* _c0t__tmp_206 = _c0_tree_add_helper(_c0v_r, _c0v_x, (_c0v_v + 1), _c0v_max, _c0v__ownedFields);
          _c0v__3 = _c0t__tmp_206;
          if (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && !(_c0v__cond_6))) {
            int _c0t__tmp_212;
            if ((_c0v_root != NULL)) {
              int _c0t__tmp_211 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
              _c0t__tmp_212 = _c0t__tmp_211;
            } else {
              _c0t__tmp_212 = -(1);
            }
            _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_212, 2, c0_string_fromliteral("Field access runtime check failed for struct Node.right"));
          }
          struct _c0_Node** _c0t__tmp_213;
          _c0t__tmp_213 = &((cc0_deref(struct _c0_Node, _c0v_root))._c0_right);
          cc0_deref(struct _c0_Node*, _c0t__tmp_213) = _c0v__3;
        } else {
          struct _c0_Node* _c0t__tmp_214 = _c0_create_tree_helper(_c0v_x, (_c0v_v + 1), _c0v_max, _c0v__ownedFields);
          _c0v__4 = _c0t__tmp_214;
          if (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && _c0v__cond_6)) {
            int _c0t__tmp_220;
            if ((_c0v_root != NULL)) {
              int _c0t__tmp_219 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
              _c0t__tmp_220 = _c0t__tmp_219;
            } else {
              _c0t__tmp_220 = -(1);
            }
            _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_220, 2, c0_string_fromliteral("Field access runtime check failed for struct Node.right"));
          }
          struct _c0_Node** _c0t__tmp_221;
          _c0t__tmp_221 = &((cc0_deref(struct _c0_Node, _c0v_root))._c0_right);
          cc0_deref(struct _c0_Node*, _c0t__tmp_221) = _c0v__4;
        }
      }
    }
    if (((((((((((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && _c0v__cond_6) && !((_c0v_root == NULL))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && _c0v__cond_6) && !((_c0v_root == NULL)))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && _c0v__cond_6) && !((_c0v_root == NULL)))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && _c0v__cond_6) && !((_c0v_root == NULL)))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && _c0v__cond_6) && !((_c0v_root == NULL)))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && !(_c0v__cond_6)) && !((_c0v_root == NULL)))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && !(_c0v__cond_6)) && !((_c0v_root == NULL)))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && !(_c0v__cond_6)) && !((_c0v_root == NULL)))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && !(_c0v__cond_6)) && !((_c0v_root == NULL)))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && !(_c0v__cond_6)) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)) && !((_c0v_root == NULL))))) {
      int _c0t__tmp_332;
      if ((_c0v_root != NULL)) {
        int _c0t__tmp_331 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
        _c0t__tmp_332 = _c0t__tmp_331;
      } else {
        _c0t__tmp_332 = -(1);
      }
      _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_332, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
    }
    if (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && _c0v__cond_6) && !((_c0v_root == NULL))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && _c0v__cond_6) && !((_c0v_root == NULL)))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && !(_c0v__cond_6)) && !((_c0v_root == NULL)))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && !(_c0v__cond_6)) && !((_c0v_root == NULL))))) {
      int _c0t__tmp_357;
      if ((_c0v_root != NULL)) {
        int _c0t__tmp_356 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
        _c0t__tmp_357 = _c0t__tmp_356;
      } else {
        _c0t__tmp_357 = -(1);
      }
      _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_357, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.left"));
    }
    if ((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && !((_c0v_root == NULL))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)) && !((_c0v_root == NULL))))) {
      int _c0t__tmp_378;
      if ((_c0v_root != NULL)) {
        int _c0t__tmp_377 = (cc0_deref(struct _c0_Node, _c0v_root))._c0__id;
        _c0t__tmp_378 = _c0t__tmp_377;
      } else {
        _c0t__tmp_378 = -(1);
      }
      _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_378, 2, c0_string_fromliteral("Field access runtime check failed for struct Node.right"));
    }
    if (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && _c0v__cond_6) && !((_c0v_root == NULL))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && !(_c0v__cond_6)) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && !((_c0v_root == NULL)))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)) && !((_c0v_root == NULL))))) {
      int _c0t__tmp_400 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
      cc0_assert((_c0t__tmp_400 >= _c0v_min), c0_string_fromliteral("src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 272.7-272.32: assert failed"));
      int _c0t__tmp_401 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
      cc0_assert((_c0t__tmp_401 <= _c0v_max), c0_string_fromliteral("src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 273.7-273.32: assert failed"));
    }
    if ((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && _c0v__cond_6) && !((_c0v_root == NULL)))) {
      int _c0t__tmp_407 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
      _c0_bst(_c0v__4, (_c0t__tmp_407 + 1), _c0v_max, _c0v__ownedFields);
    }
    if (((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && _c0v__cond_6) && !((_c0v_root == NULL))) || (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && !(_c0v__cond_6)) && !((_c0v_root == NULL))))) {
      struct _c0_Node* _c0t__tmp_419 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
      int _c0t__tmp_420 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
      _c0_bst(_c0t__tmp_419, _c0v_min, (_c0t__tmp_420 - 1), _c0v__ownedFields);
    }
    if ((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_5) && !(_c0v__cond_6)) && !((_c0v_root == NULL)))) {
      int _c0t__tmp_426 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
      _c0_bst(_c0v__3, (_c0t__tmp_426 + 1), _c0v_max, _c0v__ownedFields);
    }
    if ((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && !((_c0v_root == NULL))) || ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)) && !((_c0v_root == NULL))))) {
      struct _c0_Node* _c0t__tmp_436 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_right;
      int _c0t__tmp_437 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
      _c0_bst(_c0t__tmp_436, (_c0t__tmp_437 + 1), _c0v_max, _c0v__ownedFields);
    }
    if (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && !((_c0v_root == NULL)))) {
      int _c0t__tmp_442 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
      _c0_bst(_c0v__2, _c0v_min, (_c0t__tmp_442 - 1), _c0v__ownedFields);
    }
    if (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)) && !((_c0v_root == NULL)))) {
      int _c0t__tmp_447 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
      _c0_bst(_c0v__1, _c0v_min, (_c0t__tmp_447 - 1), _c0v__ownedFields);
    }
    int* _c0t__tmp_448 = (cc0_deref(struct _c0_OwnedFields, _c0v__ownedFields))._c0_instanceCounter;
    struct _c0_OwnedFields* _c0t__tmp_449 = _c0_initOwnedFields(_c0t__tmp_448);
    _c0v__tempFields1 = _c0t__tmp_449;
    if ((_c0v__cond_1 && _c0v__cond_2)) {
      _c0_bst(_c0v__, _c0v_min, _c0v_max, _c0v__ownedFields);
    }
    _c0_sep_bst(_c0v_root, _c0v_min, _c0v_max, _c0v__tempFields1);
    return _c0v_root;
  }
}

struct _c0_Node;
bool _c0_tree_contains(struct _c0_Node* _c0v_root, int _c0v_x, int* _c0v__instanceCounter) {
  bool _c0v_res = false;
  bool _c0t__tmp_451 = _c0_tree_contains_helper(_c0v_root, _c0v_x, -(2147483647), 2147483647, _c0v__instanceCounter);
  _c0v_res = _c0t__tmp_451;
  return _c0v_res;
}

struct _c0_Node;
bool _c0_tree_contains_helper(struct _c0_Node* _c0v_root, int _c0v_x, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  int _c0v_v = 0;
  struct _c0_Node* _c0v_l = NULL;
  struct _c0_Node* _c0v_r = NULL;
  bool _c0v_temp1 = false;
  bool _c0v_temp2 = false;
  if ((_c0v_root == NULL)) {
    return false;
  } else {
    int _c0t__tmp_452 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0v_v = _c0t__tmp_452;
    struct _c0_Node* _c0t__tmp_453 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
    _c0v_l = _c0t__tmp_453;
    struct _c0_Node* _c0t__tmp_454 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_right;
    _c0v_r = _c0t__tmp_454;
    if ((_c0v_v == _c0v_x)) {
      return true;
    } else {
      if ((_c0v_x < _c0v_v)) {
        bool _c0t__tmp_455 = _c0_tree_contains_helper(_c0v_l, _c0v_x, _c0v_min, (_c0v_v - 1), _c0v__instanceCounter);
        _c0v_temp1 = _c0t__tmp_455;
        return _c0v_temp1;
      } else {
        bool _c0t__tmp_456 = _c0_tree_contains_helper(_c0v_r, _c0v_x, (_c0v_v + 1), _c0v_max, _c0v__instanceCounter);
        _c0v_temp2 = _c0t__tmp_456;
        return _c0v_temp2;
      }
    }
  }
}

struct _c0_Node;
void _c0_tree_main_lemma(struct _c0_Node* _c0v_root, int _c0v_x, int* _c0v__instanceCounter) {
  _c0_tree_main_lemma_bst(_c0v_root, _c0v_x, -(2147483647), 2147483647, _c0v__instanceCounter);
}

struct _c0_Node;
void _c0_tree_main_lemma_bst(struct _c0_Node* _c0v_root, int _c0v_x, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  if ((_c0v_root == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_457 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
    int _c0t__tmp_458 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_tree_main_lemma_bst(_c0t__tmp_457, _c0v_x, _c0v_min, (_c0t__tmp_458 - 1), _c0v__instanceCounter);
    struct _c0_Node* _c0t__tmp_459 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_right;
    int _c0t__tmp_460 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_tree_main_lemma_bst(_c0t__tmp_459, _c0v_x, (_c0t__tmp_460 + 1), _c0v_max, _c0v__instanceCounter);
  }
}

struct _c0_Node;
int _c0_tree_max(struct _c0_Node* _c0v_root, int* _c0v__instanceCounter) {
  int _c0v_res = 0;
  int _c0t__tmp_461 = _c0_tree_max_helper(_c0v_root, -(2147483647), 2147483647, _c0v__instanceCounter);
  _c0v_res = _c0t__tmp_461;
  _c0_tree_max_lemma(_c0v_root, 2147483647, -(2147483647), _c0v_res, _c0v__instanceCounter);
  return _c0v_res;
}

struct _c0_Node;
int _c0_tree_max_helper(struct _c0_Node* _c0v_root, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  int _c0v_v = 0;
  struct _c0_Node* _c0v_r = NULL;
  int _c0v_m = 0;
  int _c0t__tmp_462 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
  _c0v_v = _c0t__tmp_462;
  struct _c0_Node* _c0t__tmp_463 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_right;
  _c0v_r = _c0t__tmp_463;
  if ((_c0v_r == NULL)) {
    return _c0v_v;
  } else {
    int _c0t__tmp_464 = _c0_tree_max_helper(_c0v_r, (_c0v_v + 1), _c0v_max, _c0v__instanceCounter);
    _c0v_m = _c0t__tmp_464;
    return _c0v_m;
  }
}

struct _c0_Node;
void _c0_tree_max_lemma(struct _c0_Node* _c0v_root, int _c0v_newMax, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  if ((_c0v_root == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_465 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_right;
    int _c0t__tmp_466 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_tree_max_lemma(_c0t__tmp_465, _c0v_newMax, (_c0t__tmp_466 + 1), _c0v_max, _c0v__instanceCounter);
  }
}

struct _c0_Node;
int _c0_tree_min(struct _c0_Node* _c0v_root, int* _c0v__instanceCounter) {
  int _c0v_res = 0;
  int _c0t__tmp_467 = _c0_tree_min_helper(_c0v_root, -(2147483647), 2147483647, _c0v__instanceCounter);
  _c0v_res = _c0t__tmp_467;
  _c0_tree_min_lemma(_c0v_root, -(2147483647), _c0v_res, 2147483647, _c0v__instanceCounter);
  return _c0v_res;
}

struct _c0_Node;
int _c0_tree_min_helper(struct _c0_Node* _c0v_root, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  int _c0v_v = 0;
  struct _c0_Node* _c0v_l = NULL;
  int _c0v_m = 0;
  int _c0t__tmp_468 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
  _c0v_v = _c0t__tmp_468;
  struct _c0_Node* _c0t__tmp_469 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
  _c0v_l = _c0t__tmp_469;
  if ((_c0v_l == NULL)) {
    return _c0v_v;
  } else {
    int _c0t__tmp_470 = _c0_tree_min_helper(_c0v_l, _c0v_min, (_c0v_v - 1), _c0v__instanceCounter);
    _c0v_m = _c0t__tmp_470;
    return _c0v_m;
  }
}

struct _c0_Node;
void _c0_tree_min_lemma(struct _c0_Node* _c0v_root, int _c0v_newMin, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  if ((_c0v_root == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_471 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
    int _c0t__tmp_472 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_tree_min_lemma(_c0t__tmp_471, _c0v_newMin, _c0v_min, (_c0t__tmp_472 - 1), _c0v__instanceCounter);
  }
}

struct _c0_Node;
struct _c0_Node* _c0_tree_remove(struct _c0_Node* _c0v_root, int _c0v_x, int* _c0v__instanceCounter) {
  struct _c0_Node* _c0v_res = NULL;
  struct _c0_Node* _c0t__tmp_473 = _c0_tree_remove_helper(_c0v_root, _c0v_x, -(2147483647), 2147483647, _c0v__instanceCounter);
  _c0v_res = _c0t__tmp_473;
  return _c0v_res;
}

struct _c0_Node;
struct _c0_Node* _c0_tree_remove_helper(struct _c0_Node* _c0v_root, int _c0v_x, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  int _c0v_v = 0;
  struct _c0_Node* _c0v_l = NULL;
  struct _c0_Node* _c0v_r = NULL;
  struct _c0_Node* _c0v__ = NULL;
  struct _c0_Node* _c0v__1 = NULL;
  int _c0v_m = 0;
  struct _c0_Node* _c0v__2 = NULL;
  if ((_c0v_root == NULL)) {
    return _c0v_root;
  } else {
    int _c0t__tmp_474 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0v_v = _c0t__tmp_474;
    struct _c0_Node* _c0t__tmp_475 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
    _c0v_l = _c0t__tmp_475;
    struct _c0_Node* _c0t__tmp_476 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_right;
    _c0v_r = _c0t__tmp_476;
    if ((_c0v_x < _c0v_v)) {
      struct _c0_Node* _c0t__tmp_477 = _c0_tree_remove_helper(_c0v_l, _c0v_x, _c0v_min, (_c0v_v - 1), _c0v__instanceCounter);
      _c0v__ = _c0t__tmp_477;
      struct _c0_Node** _c0t__tmp_478;
      _c0t__tmp_478 = &((cc0_deref(struct _c0_Node, _c0v_root))._c0_left);
      cc0_deref(struct _c0_Node*, _c0t__tmp_478) = _c0v__;
      _c0_tree_remove_lemma_right(_c0v_r, _c0v_x, (_c0v_v + 1), _c0v_max, _c0v__instanceCounter);
      return _c0v_root;
    } else {
      if ((_c0v_v < _c0v_x)) {
        struct _c0_Node* _c0t__tmp_479 = _c0_tree_remove_helper(_c0v_r, _c0v_x, (_c0v_v + 1), _c0v_max, _c0v__instanceCounter);
        _c0v__1 = _c0t__tmp_479;
        struct _c0_Node** _c0t__tmp_480;
        _c0t__tmp_480 = &((cc0_deref(struct _c0_Node, _c0v_root))._c0_right);
        cc0_deref(struct _c0_Node*, _c0t__tmp_480) = _c0v__1;
        _c0_tree_remove_lemma_left(_c0v_l, _c0v_x, _c0v_min, (_c0v_v - 1), _c0v__instanceCounter);
        return _c0v_root;
      } else {
        if ((_c0v_l == NULL)) {
          if ((_c0v_r == NULL)) {
            return NULL;
          } else {
            _c0_tree_remove_lemma_right(_c0v_r, _c0v_x, (_c0v_v + 1), _c0v_max, _c0v__instanceCounter);
            _c0_tree_remove_lemma_min(_c0v_r, _c0v_x, _c0v_min, (_c0v_v + 1), _c0v_max, _c0v__instanceCounter);
            return _c0v_r;
          }
        } else {
          if ((_c0v_r == NULL)) {
            _c0_tree_remove_lemma_left(_c0v_l, _c0v_x, _c0v_min, (_c0v_v - 1), _c0v__instanceCounter);
            _c0_tree_remove_lemma_max(_c0v_l, _c0v_x, _c0v_max, _c0v_min, (_c0v_v - 1), _c0v__instanceCounter);
            return _c0v_l;
          } else {
            int _c0t__tmp_481 = _c0_tree_max_helper(_c0v_l, _c0v_min, (_c0v_v - 1), _c0v__instanceCounter);
            _c0v_m = _c0t__tmp_481;
            int* _c0t__tmp_482;
            _c0t__tmp_482 = &((cc0_deref(struct _c0_Node, _c0v_root))._c0_val);
            cc0_deref(int, _c0t__tmp_482) = _c0v_m;
            struct _c0_Node* _c0t__tmp_483 = _c0_tree_remove_helper(_c0v_l, _c0v_m, _c0v_min, _c0v_m, _c0v__instanceCounter);
            _c0v__2 = _c0t__tmp_483;
            struct _c0_Node** _c0t__tmp_484;
            _c0t__tmp_484 = &((cc0_deref(struct _c0_Node, _c0v_root))._c0_left);
            cc0_deref(struct _c0_Node*, _c0t__tmp_484) = _c0v__2;
            struct _c0_Node* _c0t__tmp_485 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
            _c0_tree_remove_lemma(_c0t__tmp_485, _c0v_min, _c0v_m, _c0v__instanceCounter);
            struct _c0_Node* _c0t__tmp_486 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
            _c0_tree_remove_lemma_left2(_c0t__tmp_486, _c0v_x, _c0v_m, _c0v_min, (_c0v_m - 1), _c0v__instanceCounter);
            _c0_tree_remove_lemma_right(_c0v_r, _c0v_x, (_c0v_v + 1), _c0v_max, _c0v__instanceCounter);
            _c0_tree_remove_lemma_min(_c0v_r, _c0v_x, (_c0v_m + 1), (_c0v_v + 1), _c0v_max, _c0v__instanceCounter);
            return _c0v_root;
          }
        }
      }
    }
  }
}

struct _c0_Node;
void _c0_tree_remove_lemma(struct _c0_Node* _c0v_root, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  if ((_c0v_root == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_487 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_right;
    int _c0t__tmp_488 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_tree_remove_lemma(_c0t__tmp_487, (_c0t__tmp_488 + 1), _c0v_max, _c0v__instanceCounter);
  }
}

struct _c0_Node;
void _c0_tree_remove_lemma_left(struct _c0_Node* _c0v_l, int _c0v_x, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  if ((_c0v_l == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_489 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_left;
    if ((_c0t__tmp_489 == NULL)) {
      struct _c0_Node* _c0t__tmp_490 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_right;
      int _c0t__tmp_491 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_val;
      _c0_tree_remove_lemma_left(_c0t__tmp_490, _c0v_x, (_c0t__tmp_491 + 1), _c0v_max, _c0v__instanceCounter);
    } else {
      struct _c0_Node* _c0t__tmp_492 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_right;
      if ((_c0t__tmp_492 == NULL)) {
        struct _c0_Node* _c0t__tmp_493 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_left;
        int _c0t__tmp_494 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_val;
        _c0_tree_remove_lemma_left(_c0t__tmp_493, _c0v_x, _c0v_min, (_c0t__tmp_494 - 1), _c0v__instanceCounter);
      } else {
        struct _c0_Node* _c0t__tmp_495 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_right;
        int _c0t__tmp_496 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_val;
        _c0_tree_remove_lemma_left(_c0t__tmp_495, _c0v_x, (_c0t__tmp_496 + 1), _c0v_max, _c0v__instanceCounter);
        struct _c0_Node* _c0t__tmp_497 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_left;
        int _c0t__tmp_498 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_val;
        _c0_tree_remove_lemma_left(_c0t__tmp_497, _c0v_x, _c0v_min, (_c0t__tmp_498 - 1), _c0v__instanceCounter);
      }
    }
  }
}

struct _c0_Node;
void _c0_tree_remove_lemma_left2(struct _c0_Node* _c0v_l, int _c0v_newX, int _c0v_x, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  if ((_c0v_l == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_499 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_left;
    if ((_c0t__tmp_499 == NULL)) {
      struct _c0_Node* _c0t__tmp_500 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_right;
      int _c0t__tmp_501 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_val;
      _c0_tree_remove_lemma_left2(_c0t__tmp_500, _c0v_newX, _c0v_x, (_c0t__tmp_501 + 1), _c0v_max, _c0v__instanceCounter);
    } else {
      struct _c0_Node* _c0t__tmp_502 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_right;
      if ((_c0t__tmp_502 == NULL)) {
        struct _c0_Node* _c0t__tmp_503 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_left;
        int _c0t__tmp_504 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_val;
        _c0_tree_remove_lemma_left2(_c0t__tmp_503, _c0v_newX, _c0v_x, _c0v_min, (_c0t__tmp_504 - 1), _c0v__instanceCounter);
      } else {
        struct _c0_Node* _c0t__tmp_505 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_right;
        int _c0t__tmp_506 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_val;
        _c0_tree_remove_lemma_left2(_c0t__tmp_505, _c0v_newX, _c0v_x, (_c0t__tmp_506 + 1), _c0v_max, _c0v__instanceCounter);
        struct _c0_Node* _c0t__tmp_507 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_left;
        int _c0t__tmp_508 = (cc0_deref(struct _c0_Node, _c0v_l))._c0_val;
        _c0_tree_remove_lemma_left2(_c0t__tmp_507, _c0v_newX, _c0v_x, _c0v_min, (_c0t__tmp_508 - 1), _c0v__instanceCounter);
      }
    }
  }
}

struct _c0_Node;
void _c0_tree_remove_lemma_max(struct _c0_Node* _c0v_root, int _c0v_x, int _c0v_newMax, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  if ((_c0v_root == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_509 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_right;
    int _c0t__tmp_510 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_tree_remove_lemma_max(_c0t__tmp_509, _c0v_x, _c0v_newMax, (_c0t__tmp_510 + 1), _c0v_max, _c0v__instanceCounter);
  }
}

struct _c0_Node;
void _c0_tree_remove_lemma_min(struct _c0_Node* _c0v_root, int _c0v_x, int _c0v_newMin, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  if ((_c0v_root == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_511 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_left;
    int _c0t__tmp_512 = (cc0_deref(struct _c0_Node, _c0v_root))._c0_val;
    _c0_tree_remove_lemma_min(_c0t__tmp_511, _c0v_x, _c0v_newMin, _c0v_min, (_c0t__tmp_512 - 1), _c0v__instanceCounter);
  }
}

struct _c0_Node;
void _c0_tree_remove_lemma_right(struct _c0_Node* _c0v_r, int _c0v_x, int _c0v_min, int _c0v_max, int* _c0v__instanceCounter) {
  if ((_c0v_r == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_513 = (cc0_deref(struct _c0_Node, _c0v_r))._c0_left;
    if ((_c0t__tmp_513 == NULL)) {
      struct _c0_Node* _c0t__tmp_514 = (cc0_deref(struct _c0_Node, _c0v_r))._c0_right;
      int _c0t__tmp_515 = (cc0_deref(struct _c0_Node, _c0v_r))._c0_val;
      _c0_tree_remove_lemma_right(_c0t__tmp_514, _c0v_x, (_c0t__tmp_515 + 1), _c0v_max, _c0v__instanceCounter);
    } else {
      struct _c0_Node* _c0t__tmp_516 = (cc0_deref(struct _c0_Node, _c0v_r))._c0_right;
      if ((_c0t__tmp_516 == NULL)) {
        struct _c0_Node* _c0t__tmp_517 = (cc0_deref(struct _c0_Node, _c0v_r))._c0_left;
        int _c0t__tmp_518 = (cc0_deref(struct _c0_Node, _c0v_r))._c0_val;
        _c0_tree_remove_lemma_right(_c0t__tmp_517, _c0v_x, _c0v_min, (_c0t__tmp_518 - 1), _c0v__instanceCounter);
      } else {
        struct _c0_Node* _c0t__tmp_519 = (cc0_deref(struct _c0_Node, _c0v_r))._c0_right;
        int _c0t__tmp_520 = (cc0_deref(struct _c0_Node, _c0v_r))._c0_val;
        _c0_tree_remove_lemma_right(_c0t__tmp_519, _c0v_x, (_c0t__tmp_520 + 1), _c0v_max, _c0v__instanceCounter);
        struct _c0_Node* _c0t__tmp_521 = (cc0_deref(struct _c0_Node, _c0v_r))._c0_left;
        int _c0t__tmp_522 = (cc0_deref(struct _c0_Node, _c0v_r))._c0_val;
        _c0_tree_remove_lemma_right(_c0t__tmp_521, _c0v_x, _c0v_min, (_c0t__tmp_522 - 1), _c0v__instanceCounter);
      }
    }
  }
}
long map_length = 1306;
const char* source_map[1306] = {
  [67] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 15.12-15.31",
  [75] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 20.3-20.26",
  [76] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 20.3-20.44",
  [79] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 22.3-22.19",
  [80] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 22.22-22.48",
  [81] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 22.3-22.48",
  [83] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 23.3-23.19",
  [84] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 23.47-23.63",
  [86] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 23.3-23.64",
  [90] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 25.22-25.38",
  [96] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 26.5-26.21",
  [98] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 26.5-26.24",
  [99] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 26.5-26.31",
  [108] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 34.21-34.37",
  [111] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 35.3-35.19",
  [112] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 35.22-35.48",
  [113] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 35.3-35.48",
  [114] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 36.56-36.72",
  [122] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 38.8-38.24",
  [123] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 38.8-38.27",
  [125] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 38.40-38.56",
  [126] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 38.40-38.59",
  [127] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 38.40-38.68",
  [133] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 39.19-39.35",
  [134] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 39.19-39.38",
  [135] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 39.19-39.43",
  [137] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 40.34-40.50",
  [138] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 40.24-40.51",
  [141] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 41.15-41.36",
  [146] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 42.41-42.57",
  [147] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 42.24-42.57",
  [151] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 44.9-44.30",
  [152] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 44.33-44.49",
  [153] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 44.33-44.52",
  [154] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 44.9-44.52",
  [161] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 47.3-47.19",
  [162] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 47.3-47.33",
  [167] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 52.27-52.43",
  [168] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 52.17-52.44",
  [171] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 53.11-53.27",
  [172] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 53.11-53.34",
  [178] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 54.13-54.29",
  [179] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 54.13-54.36",
  [180] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 54.13-54.45",
  [182] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 54.49-54.65",
  [183] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 54.49-54.72",
  [184] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 54.49-54.77",
  [190] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 55.20-55.36",
  [191] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 55.20-55.43",
  [194] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 57.35-57.51",
  [195] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 57.21-57.51",
  [204] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 68.6-68.20",
  [205] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 68.24-68.40",
  [207] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 68.51-68.63",
  [209] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 70.30-70.46",
  [210] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 70.20-70.47",
  [214] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.9-71.25",
  [215] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.9-71.37",
  [217] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.50-71.66",
  [218] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.50-71.78",
  [219] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.50-71.87",
  [228] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.121-71.137",
  [229] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.102-71.137",
  [234] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 74.3-74.19",
  [236] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 74.3-74.31",
  [237] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 74.3-74.39",
  [238] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 75.3-75.22",
  [240] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 77.3-77.18",
  [242] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 77.3-77.49",
  [244] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 78.3-78.16",
  [245] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 78.3-78.28",
  [247] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 79.3-79.13",
  [248] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 79.3-79.19",
  [250] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 80.3-80.17",
  [251] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 80.3-80.25",
  [255] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 82.20-82.33",
  [261] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 83.5-83.20",
  [263] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 83.5-83.23",
  [264] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 83.5-83.32",
  [271] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 86.5-86.25",
  [272] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 86.28-86.41",
  [273] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 86.5-86.41",
  [276] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 88.5-88.25",
  [277] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 88.5-88.29",
  [279] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 90.10-90.26",
  [280] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 90.10-90.38",
  [285] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 94.28-94.51",
  [286] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 94.27-94.51",
  [287] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 94.5-94.69",
  [288] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 95.7-95.30",
  [289] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 95.5-95.36",
  [290] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 96.14-96.37",
  [291] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 96.12-96.38",
  [296] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 100.24-100.41",
  [299] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 102.9-102.24",
  [300] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 102.9-102.36",
  [302] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 103.9-103.34",
  [303] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 104.9-104.24",
  [305] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 104.9-104.36",
  [306] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 104.9-104.43",
  [309] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 107.13-107.57",
  [311] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 108.5-108.20",
  [313] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 108.5-108.32",
  [314] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 108.5-108.39",
  [315] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 109.5-109.30",
  [320] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 114.27-114.44",
  [326] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 115.28-115.45",
  [327] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 115.28-115.57",
  [331] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 116.9-116.29",
  [337] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 121.27-121.44",
  [340] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 123.19-123.63",
  [343] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 124.16-124.33",
  [344] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 124.16-124.45",
  [346] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 125.9-125.29",
  [350] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 127.5-127.22",
  [352] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 127.5-127.34",
  [353] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 127.5-127.41",
  [354] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 128.5-128.32",
  [358] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 132.27-132.44",
  [361] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 134.26-134.40",
  [363] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 135.13-135.85",
  [366] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 136.18-136.34",
  [367] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 136.18-136.46",
  [369] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 137.13-137.29",
  [371] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 137.13-137.41",
  [372] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 137.13-137.49",
  [373] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 138.13-138.39",
  [376] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 140.12-140.33",
  [379] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 140.40-140.55",
  [380] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 140.40-140.62",
  [389] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 146.26-146.42",
  [395] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 147.38-147.54",
  [396] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 147.38-147.57",
  [401] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 149.35-149.53",
  [407] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 150.36-150.51",
  [408] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 150.53-150.71",
  [409] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 150.21-150.75",
  [464] = "/usr/share/cc0/lib/util.c0: 40.21-40.34",
  [465] = "/usr/share/cc0/lib/util.c0: 40.12-40.39",
  [469] = "/usr/share/cc0/lib/util.c0: 42.21-42.34",
  [470] = "/usr/share/cc0/lib/util.c0: 42.12-42.44",
  [479] = "/usr/share/cc0/lib/util.c0: 51.18-51.28",
  [484] = "/usr/share/cc0/lib/util.c0: 53.3-53.12",
  [485] = "/usr/share/cc0/lib/util.c0: 53.3-53.19",
  [491] = "/usr/share/cc0/lib/util.c0: 57.7-57.20",
  [492] = "/usr/share/cc0/lib/util.c0: 57.23-57.43",
  [493] = "/usr/share/cc0/lib/util.c0: 57.7-57.43",
  [499] = "/usr/share/cc0/lib/util.c0: 60.10-60.34",
  [505] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/stress.c0: 4.16-4.21",
  [506] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/stress.c0: 4.12-4.22",
  [512] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/stress.c0: 9.12-9.38",
  [587] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 45.26-45.35",
  [588] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 45.5-45.42",
  [589] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 46.26-46.35",
  [590] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 46.5-46.42",
  [591] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 47.26-47.35",
  [592] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 47.5-47.42",
  [593] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 48.13-48.23",
  [594] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 48.30-48.39",
  [595] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 48.5-48.58",
  [596] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 49.13-49.24",
  [597] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 49.26-49.35",
  [598] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 49.5-49.59",
  [605] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 55.3-55.55",
  [612] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 62.5-62.18",
  [616] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 66.44-66.53",
  [621] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 66.5-66.120",
  [624] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 67.44-67.53",
  [629] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 67.5-67.121",
  [632] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 68.44-68.53",
  [637] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 68.5-68.119",
  [638] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 69.12-69.21",
  [639] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 69.5-69.30",
  [640] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 70.12-70.21",
  [641] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 70.5-70.30",
  [642] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 71.9-71.19",
  [643] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 71.26-71.35",
  [644] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 71.5-71.54",
  [645] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 72.9-72.20",
  [646] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 72.22-72.31",
  [647] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 72.5-72.55",
  [654] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 79.9-79.71",
  [656] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 80.3-80.50",
  [666] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 88.3-88.12",
  [667] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 88.15-88.44",
  [668] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 88.3-88.44",
  [670] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 89.3-89.12",
  [671] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 89.3-89.18",
  [673] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 90.3-90.13",
  [674] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 90.3-90.20",
  [676] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 91.3-91.14",
  [677] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 91.3-91.21",
  [707] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 122.17-122.50",
  [709] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 123.8-123.48",
  [713] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 127.9-127.19",
  [716] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 129.13-129.39",
  [718] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 130.20-130.53",
  [720] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 131.11-131.44",
  [722] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 132.12-132.55",
  [724] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 133.5-133.18",
  [730] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 140.10-140.20",
  [733] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 142.16-142.43",
  [735] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 143.11-143.54",
  [737] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 144.5-144.53",
  [738] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 145.13-145.59",
  [740] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 146.5-146.20",
  [753] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 157.55-157.64",
  [758] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 157.5-157.130",
  [761] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 158.55-158.64",
  [766] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 158.5-158.131",
  [769] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 159.55-159.64",
  [774] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 159.5-159.129",
  [775] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 160.13-160.23",
  [776] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 160.30-160.39",
  [777] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 160.5-160.58",
  [778] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 161.13-161.24",
  [779] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 161.26-161.35",
  [780] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 161.5-161.59",
  [788] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 168.3-168.31",
  [789] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 169.9-169.72",
  [816] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 195.9-195.54",
  [818] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 196.35-196.64",
  [819] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 196.19-196.65",
  [822] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 199.7-199.37",
  [824] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 201.5-201.38",
  [827] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 206.9-206.18",
  [829] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 207.9-207.19",
  [831] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 208.9-208.20",
  [837] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 215.14-215.61",
  [842] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 218.50-218.59",
  [847] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 218.11-218.126",
  [850] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 220.9-220.19",
  [851] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 220.9-220.24",
  [853] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 224.14-224.61",
  [858] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 227.50-227.59",
  [863] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 227.11-227.126",
  [866] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 229.9-229.19",
  [867] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 229.9-229.24",
  [874] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 240.16-240.63",
  [879] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 243.52-243.61",
  [884] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 243.13-243.129",
  [887] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 245.11-245.22",
  [888] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 245.11-245.27",
  [890] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 249.16-249.63",
  [895] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 252.52-252.61",
  [900] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 252.13-252.129",
  [903] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 254.11-254.22",
  [904] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 254.11-254.27",
  [911] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 260.46-260.55",
  [916] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 260.7-260.121",
  [921] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 264.46-264.55",
  [926] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 264.7-264.122",
  [931] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 268.46-268.55",
  [936] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 268.7-268.123",
  [939] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 272.14-272.23",
  [940] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 272.7-272.32",
  [941] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 273.14-273.23",
  [942] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 273.7-273.32",
  [945] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 277.15-277.24",
  [946] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 277.7-277.48",
  [949] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 281.11-281.21",
  [950] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 281.28-281.37",
  [951] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 281.7-281.56",
  [954] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 285.15-285.24",
  [955] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 285.7-285.48",
  [958] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 289.11-289.22",
  [959] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 289.24-289.33",
  [960] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 289.7-289.57",
  [963] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 293.20-293.29",
  [964] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 293.7-293.48",
  [967] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 297.20-297.29",
  [968] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 297.7-297.48",
  [970] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 299.36-299.65",
  [971] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 299.20-299.66",
  [974] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 302.7-302.37",
  [976] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 304.5-304.42",
  [984] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 312.9-312.81",
  [999] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 329.9-329.18",
  [1001] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 330.9-330.19",
  [1003] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 331.9-331.20",
  [1009] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 340.17-340.73",
  [1013] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 345.17-345.73",
  [1023] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 354.3-354.74",
  [1030] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 364.25-364.35",
  [1031] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 364.45-364.54",
  [1032] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 364.5-364.77",
  [1033] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 365.25-365.36",
  [1034] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 365.41-365.50",
  [1035] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 365.5-365.78",
  [1042] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 372.9-372.73",
  [1044] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 373.3-373.71",
  [1053] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 382.7-382.16",
  [1055] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 383.7-383.18",
  [1060] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 390.9-390.57",
  [1070] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 402.20-402.31",
  [1071] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 402.41-402.50",
  [1072] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 402.5-402.78",
  [1079] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 409.9-409.73",
  [1081] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 410.3-410.71",
  [1090] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 419.7-419.16",
  [1092] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 420.7-420.17",
  [1097] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 427.9-427.57",
  [1107] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 439.20-439.30",
  [1108] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 439.45-439.54",
  [1109] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 439.5-439.77",
  [1116] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 446.9-446.79",
  [1133] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 465.9-465.18",
  [1135] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 466.9-466.19",
  [1137] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 467.9-467.20",
  [1140] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 470.11-470.65",
  [1143] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 471.7-471.17",
  [1144] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 471.7-471.21",
  [1145] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 472.7-472.66",
  [1149] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 479.14-479.68",
  [1152] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 480.9-480.20",
  [1153] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 480.9-480.25",
  [1154] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 481.9-481.67",
  [1161] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 494.13-494.72",
  [1162] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 495.13-495.75",
  [1167] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 503.13-503.71",
  [1168] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 504.13-504.75",
  [1171] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 509.17-509.65",
  [1174] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 510.13-510.22",
  [1175] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 510.13-510.26",
  [1176] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 511.18-511.68",
  [1179] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 512.13-512.23",
  [1180] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 512.13-512.28",
  [1181] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 513.31-513.41",
  [1182] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 513.13-513.68",
  [1183] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 514.37-514.47",
  [1184] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 514.13-514.84",
  [1185] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 515.13-515.72",
  [1186] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 516.13-516.77",
  [1199] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 532.23-532.34",
  [1200] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 532.36-532.45",
  [1201] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 532.5-532.73",
  [1209] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 543.9-543.16",
  [1211] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 545.30-545.38",
  [1212] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 545.43-545.49",
  [1213] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 545.7-545.77",
  [1215] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 549.11-549.19",
  [1217] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 551.32-551.39",
  [1218] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 551.49-551.55",
  [1219] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 551.9-551.78",
  [1221] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 555.32-555.40",
  [1222] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 555.45-555.51",
  [1223] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 555.9-555.79",
  [1224] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 556.32-556.39",
  [1225] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 556.49-556.55",
  [1226] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 556.9-556.78",
  [1236] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 569.9-569.16",
  [1238] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 571.31-571.39",
  [1239] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 571.50-571.56",
  [1240] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 571.7-571.84",
  [1242] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 575.11-575.19",
  [1244] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 577.33-577.40",
  [1245] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 577.56-577.62",
  [1246] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 577.9-577.85",
  [1248] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 581.33-581.41",
  [1249] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 581.52-581.58",
  [1250] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 581.9-581.86",
  [1251] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 582.33-582.40",
  [1252] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 582.56-582.62",
  [1253] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 582.9-582.85",
  [1263] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 595.27-595.38",
  [1264] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 595.51-595.60",
  [1265] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 595.5-595.88",
  [1273] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 606.27-606.37",
  [1274] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 606.55-606.64",
  [1275] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 606.5-606.87",
  [1283] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 617.9-617.16",
  [1285] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 619.31-619.39",
  [1286] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 619.44-619.50",
  [1287] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 619.7-619.78",
  [1289] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 623.11-623.19",
  [1291] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 625.33-625.40",
  [1292] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 625.50-625.56",
  [1293] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 625.9-625.79",
  [1295] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 629.33-629.41",
  [1296] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 629.46-629.52",
  [1297] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 629.9-629.80",
  [1298] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 630.33-630.40",
  [1299] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 630.50-630.56",
  [1300] = "src/test/resources/runtime-analysis/quant-examples/bst.verified.c0: 630.9-630.79"
};
