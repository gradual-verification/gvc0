#include "cc0lib.h"
#include "c0rt.h"
#include "stack.verified.c0.h"

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
struct _c0_Node;
struct _c0_Node {
  int _c0_val;
  struct _c0_Node* _c0_next;
  int _c0__id;
};
struct _c0_Node;
struct _c0_OwnedFields;
struct _c0_OwnedFields;
void _c0_add_remove_seg(struct _c0_Node* _c0v_start, struct _c0_OwnedFields* _c0v__ownedFields, struct _c0_OwnedFields* _c0v__tempFields);
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
struct _c0_OwnedFields;
void _c0_add_remove_segHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, struct _c0_OwnedFields* _c0v__ownedFields, struct _c0_OwnedFields* _c0v__tempFields);
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_seg(struct _c0_Node* _c0v_start, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_segHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_Node;
struct _c0_Node;
void _c0_appendLemmaAfterLoopBody(struct _c0_Node* _c0v_a, struct _c0_Node* _c0v_b, struct _c0_Node* _c0v_c, int* _c0v__instanceCounter);
struct _c0_Node;
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_appendLemmaLoopBody(struct _c0_Node* _c0v_a, struct _c0_Node* _c0v_b, struct _c0_Node* _c0v_c, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node* _c0_create_list(int _c0v_val, int* _c0v__instanceCounter);
int _c0_main();
struct _c0_Node;
struct _c0_OwnedFields;
int _c0_pop(struct _c0_Node* _c0v_head, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_OwnedFields;
struct _c0_Node* _c0_push(struct _c0_Node* _c0v_head, int _c0v_val, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_remove_segHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_segHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sep_segHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, struct _c0_OwnedFields* _c0v__ownedFields);

struct _c0_Node;
struct _c0_OwnedFields;
struct _c0_OwnedFields;
void _c0_add_remove_seg(struct _c0_Node* _c0v_start, struct _c0_OwnedFields* _c0v__ownedFields, struct _c0_OwnedFields* _c0v__tempFields) {
  _c0_add_remove_segHelper(_c0v_start, NULL, _c0v__ownedFields, _c0v__tempFields);
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
struct _c0_OwnedFields;
void _c0_add_remove_segHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, struct _c0_OwnedFields* _c0v__ownedFields, struct _c0_OwnedFields* _c0v__tempFields) {
  if (!((_c0v_start == _c0v_end))) {
    int _c0t__tmp_117 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_addAcc(_c0v__ownedFields, _c0t__tmp_117, 3, 0);
    int _c0t__tmp_118 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_loseAcc(_c0v__tempFields, _c0t__tmp_118, 0);
    int _c0t__tmp_119 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_addAcc(_c0v__ownedFields, _c0t__tmp_119, 3, 1);
    int _c0t__tmp_120 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_loseAcc(_c0v__tempFields, _c0t__tmp_120, 1);
    struct _c0_Node* _c0t__tmp_121 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    _c0_add_remove_segHelper(_c0t__tmp_121, _c0v_end, _c0v__ownedFields, _c0v__tempFields);
  }
}

struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_seg(struct _c0_Node* _c0v_start, struct _c0_OwnedFields* _c0v__ownedFields) {
  _c0_add_segHelper(_c0v_start, NULL, _c0v__ownedFields);
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_segHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, struct _c0_OwnedFields* _c0v__ownedFields) {
  if (!((_c0v_start == _c0v_end))) {
    int _c0t__tmp_122 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_addAcc(_c0v__ownedFields, _c0t__tmp_122, 3, 0);
    int _c0t__tmp_123 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_addAcc(_c0v__ownedFields, _c0t__tmp_123, 3, 1);
    struct _c0_Node* _c0t__tmp_124 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    _c0_add_segHelper(_c0t__tmp_124, _c0v_end, _c0v__ownedFields);
  }
}

struct _c0_Node;
struct _c0_Node;
struct _c0_Node;
void _c0_appendLemmaAfterLoopBody(struct _c0_Node* _c0v_a, struct _c0_Node* _c0v_b, struct _c0_Node* _c0v_c, int* _c0v__instanceCounter) {
  if ((_c0v_b == _c0v_c)) {
  } else {
    if ((_c0v_a == _c0v_b)) {
    } else {
      struct _c0_Node* _c0t__tmp_125 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_next;
      _c0_appendLemmaAfterLoopBody(_c0t__tmp_125, _c0v_b, _c0v_c, _c0v__instanceCounter);
    }
  }
}

struct _c0_Node;
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_appendLemmaLoopBody(struct _c0_Node* _c0v_a, struct _c0_Node* _c0v_b, struct _c0_Node* _c0v_c, struct _c0_OwnedFields* _c0v__ownedFields) {
  bool _c0v__cond_1 = false;
  bool _c0v__cond_2 = false;
  bool _c0v__cond_3 = false;
  bool _c0v__cond_4 = false;
  _c0v__cond_1 = (_c0v_b == _c0v_c);
  if ((_c0v_b == _c0v_c)) {
  } else {
    _c0v__cond_2 = (_c0v_a == _c0v_b);
    if ((_c0v_a == _c0v_b)) {
      _c0v__cond_3 = (_c0v_b == _c0v_a);
      if (((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !((_c0v_b == _c0v_c))) || (((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !((_c0v_b == _c0v_c))))) {
        int _c0t__tmp_134;
        if ((_c0v_b != NULL)) {
          int _c0t__tmp_133 = (cc0_deref(struct _c0_Node, _c0v_b))._c0__id;
          _c0t__tmp_134 = _c0t__tmp_133;
        } else {
          _c0t__tmp_134 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_134, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
      }
      if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !((_c0v_b == _c0v_c)))) {
        int _c0t__tmp_139;
        if ((_c0v_b != NULL)) {
          int _c0t__tmp_138 = (cc0_deref(struct _c0_Node, _c0v_b))._c0__id;
          _c0t__tmp_139 = _c0t__tmp_138;
        } else {
          _c0t__tmp_139 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_139, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
      }
      if (((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !((_c0v_b == _c0v_c))) || (((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !((_c0v_b == _c0v_c))))) {
        cc0_assert(!((_c0v_b == NULL)), c0_string_fromliteral("src/test/resources/runtime-analysis/stack.verified.c0: 101.9-101.30: assert failed"));
      }
      if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !((_c0v_b == _c0v_c)))) {
        struct _c0_Node* _c0t__tmp_150 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_next;
        _c0_segHelper(_c0t__tmp_150, _c0v_c, _c0v__ownedFields);
      }
    } else {
      _c0v__cond_4 = (_c0v_a == _c0v_b);
      struct _c0_Node* _c0t__tmp_151 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_next;
      _c0_appendLemmaLoopBody(_c0t__tmp_151, _c0v_b, _c0v_c, _c0v__ownedFields);
      if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_4)) && !((_c0v_a == _c0v_c)))) {
        int _c0t__tmp_156;
        if ((_c0v_a != NULL)) {
          int _c0t__tmp_155 = (cc0_deref(struct _c0_Node, _c0v_a))._c0__id;
          _c0t__tmp_156 = _c0t__tmp_155;
        } else {
          _c0t__tmp_156 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_156, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
      }
      if (((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_4)) && !((_c0v_a == _c0v_c))) || (((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_4)) && !((_c0v_a == _c0v_c))))) {
        int _c0t__tmp_165;
        if ((_c0v_a != NULL)) {
          int _c0t__tmp_164 = (cc0_deref(struct _c0_Node, _c0v_a))._c0__id;
          _c0t__tmp_165 = _c0t__tmp_164;
        } else {
          _c0t__tmp_165 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_165, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
      }
      if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_4)) && !((_c0v_a == _c0v_c)))) {
        struct _c0_Node* _c0t__tmp_169 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_next;
        _c0_segHelper(_c0t__tmp_169, _c0v_c, _c0v__ownedFields);
      }
    }
  }
}

struct _c0_Node* _c0_create_list(int _c0v_val, int* _c0v__instanceCounter) {
  struct _c0_Node* _c0v_n = NULL;
  struct _c0_Node* _c0t__tmp_170 = cc0_alloc(struct _c0_Node);
  _c0v_n = _c0t__tmp_170;
  int* _c0t__tmp_171;
  _c0t__tmp_171 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0__id);
  int _c0t__tmp_172 = cc0_deref(int, _c0v__instanceCounter);
  cc0_deref(int, _c0t__tmp_171) = _c0t__tmp_172;
  int _c0t__tmp_173 = cc0_deref(int, _c0v__instanceCounter);
  cc0_deref(int, _c0v__instanceCounter) = (_c0t__tmp_173 + 1);
  int* _c0t__tmp_174;
  _c0t__tmp_174 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_val);
  cc0_deref(int, _c0t__tmp_174) = _c0v_val;
  struct _c0_Node** _c0t__tmp_175;
  _c0t__tmp_175 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_next);
  cc0_deref(struct _c0_Node*, _c0t__tmp_175) = NULL;
  return _c0v_n;
}

int _c0_main() {
  struct _c0_Node* _c0v_l = NULL;
  struct _c0_Node* _c0v_l2 = NULL;
  int* _c0v__instanceCounter = NULL;
  struct _c0_OwnedFields* _c0v__ownedFields = NULL;
  struct _c0_OwnedFields* _c0v__tempFields = NULL;
  int* _c0t__tmp_176 = cc0_alloc(int);
  _c0v__instanceCounter = _c0t__tmp_176;
  struct _c0_OwnedFields* _c0t__tmp_177 = _c0_initOwnedFields(_c0v__instanceCounter);
  _c0v__ownedFields = _c0t__tmp_177;
  struct _c0_Node* _c0t__tmp_178 = _c0_create_list(5, _c0v__instanceCounter);
  _c0v_l = _c0t__tmp_178;
  _c0_add_seg(_c0v_l, _c0v__ownedFields);
  struct _c0_OwnedFields* _c0t__tmp_179 = _c0_initOwnedFields(_c0v__instanceCounter);
  _c0v__tempFields = _c0t__tmp_179;
  _c0_add_remove_seg(_c0v_l, _c0v__tempFields, _c0v__ownedFields);
  struct _c0_Node* _c0t__tmp_180 = _c0_push(_c0v_l, 1, _c0v__tempFields);
  _c0v_l2 = _c0t__tmp_180;
  _c0_add_seg(_c0v_l2, _c0v__ownedFields);
  _c0_pop(_c0v_l2, _c0v__ownedFields);
  return 1;
}

struct _c0_Node;
struct _c0_OwnedFields;
int _c0_pop(struct _c0_Node* _c0v_head, struct _c0_OwnedFields* _c0v__ownedFields) {
  struct _c0_Node* _c0v_curr = NULL;
  struct _c0_Node* _c0v_prev = NULL;
  bool _c0v__cond_1 = false;
  bool _c0v__cond_2 = false;
  bool _c0v__cond_3 = false;
  bool _c0v__cond_4 = false;
  bool _c0v__cond_5 = false;
  struct _c0_OwnedFields* _c0v__tempFields = NULL;
  struct _c0_OwnedFields* _c0v__tempFields1 = NULL;
  _c0v__cond_1 = (_c0v_head == NULL);
  if ((_c0v_head == NULL)) {
    return -(1);
  } else {
    _c0v_curr = _c0v_head;
    int* _c0t__tmp_181 = (cc0_deref(struct _c0_OwnedFields, _c0v__ownedFields))._c0_instanceCounter;
    struct _c0_OwnedFields* _c0t__tmp_182 = _c0_initOwnedFields(_c0t__tmp_181);
    _c0v__tempFields1 = _c0t__tmp_182;
    bool _c0t__tmp_187;
    bool _c0t__tmp_184;
    if (!(_c0v__cond_1)) {
      struct _c0_Node* _c0t__tmp_183 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
      _c0t__tmp_184 = !((_c0t__tmp_183 == NULL));
    } else {
      _c0t__tmp_184 = false;
    }
    if (_c0t__tmp_184) {
      _c0t__tmp_187 = true;
    } else {
      bool _c0t__tmp_186;
      if (!(_c0v__cond_1)) {
        struct _c0_Node* _c0t__tmp_185 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
        _c0t__tmp_186 = !((_c0t__tmp_185 == NULL));
      } else {
        _c0t__tmp_186 = false;
      }
      _c0t__tmp_187 = _c0t__tmp_186;
    }
    if (((_c0t__tmp_187 || !(_c0v__cond_1)) || !(_c0v__cond_1))) {
      int _c0t__tmp_191;
      if ((_c0v_head != NULL)) {
        int _c0t__tmp_190 = (cc0_deref(struct _c0_Node, _c0v_head))._c0__id;
        _c0t__tmp_191 = _c0t__tmp_190;
      } else {
        _c0t__tmp_191 = -(1);
      }
      _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_191, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
    }
    if (!(_c0v__cond_1)) {
      int _c0t__tmp_193;
      if ((_c0v_head != NULL)) {
        int _c0t__tmp_192 = (cc0_deref(struct _c0_Node, _c0v_head))._c0__id;
        _c0t__tmp_193 = _c0t__tmp_192;
      } else {
        _c0t__tmp_193 = -(1);
      }
      _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_193, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
    }
    bool _c0t__tmp_195;
    if (!(_c0v__cond_1)) {
      struct _c0_Node* _c0t__tmp_194 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
      _c0t__tmp_195 = !((_c0t__tmp_194 == NULL));
    } else {
      _c0t__tmp_195 = false;
    }
    if (_c0t__tmp_195) {
      int _c0t__tmp_199;
      struct _c0_Node* _c0t__tmp_196 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
      if ((_c0t__tmp_196 != NULL)) {
        struct _c0_Node* _c0t__tmp_197 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
        int _c0t__tmp_198 = (cc0_deref(struct _c0_Node, _c0t__tmp_197))._c0__id;
        _c0t__tmp_199 = _c0t__tmp_198;
      } else {
        _c0t__tmp_199 = -(1);
      }
      _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_199, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
      int _c0t__tmp_203;
      struct _c0_Node* _c0t__tmp_200 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
      if ((_c0t__tmp_200 != NULL)) {
        struct _c0_Node* _c0t__tmp_201 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
        int _c0t__tmp_202 = (cc0_deref(struct _c0_Node, _c0t__tmp_201))._c0__id;
        _c0t__tmp_203 = _c0t__tmp_202;
      } else {
        _c0t__tmp_203 = -(1);
      }
      _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_203, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
    }
    bool _c0t__tmp_208;
    bool _c0t__tmp_205;
    if (!(_c0v__cond_1)) {
      struct _c0_Node* _c0t__tmp_204 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
      _c0t__tmp_205 = !((_c0t__tmp_204 == NULL));
    } else {
      _c0t__tmp_205 = false;
    }
    if (_c0t__tmp_205) {
      _c0t__tmp_208 = true;
    } else {
      bool _c0t__tmp_207;
      if (!(_c0v__cond_1)) {
        struct _c0_Node* _c0t__tmp_206 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
        _c0t__tmp_207 = !((_c0t__tmp_206 == NULL));
      } else {
        _c0t__tmp_207 = false;
      }
      _c0t__tmp_208 = _c0t__tmp_207;
    }
    if (_c0t__tmp_208) {
      struct _c0_Node* _c0t__tmp_209 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
      cc0_assert(!((_c0t__tmp_209 == NULL)), c0_string_fromliteral("src/test/resources/runtime-analysis/stack.verified.c0: 193.7-193.37: assert failed"));
    }
    int _c0t__tmp_211;
    if ((_c0v_curr != NULL)) {
      int _c0t__tmp_210 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
      _c0t__tmp_211 = _c0t__tmp_210;
    } else {
      _c0t__tmp_211 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__tempFields1, _c0t__tmp_211, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
    int _c0t__tmp_213;
    if ((_c0v_curr != NULL)) {
      int _c0t__tmp_212 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
      _c0t__tmp_213 = _c0t__tmp_212;
    } else {
      _c0t__tmp_213 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__tempFields1, _c0t__tmp_213, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
    struct _c0_Node* _c0t__tmp_214 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
    if (!((_c0t__tmp_214 == NULL))) {
      int _c0t__tmp_218;
      struct _c0_Node* _c0t__tmp_215 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      if ((_c0t__tmp_215 != NULL)) {
        struct _c0_Node* _c0t__tmp_216 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        int _c0t__tmp_217 = (cc0_deref(struct _c0_Node, _c0t__tmp_216))._c0__id;
        _c0t__tmp_218 = _c0t__tmp_217;
      } else {
        _c0t__tmp_218 = -(1);
      }
      _c0_addAccEnsureSeparate(_c0v__tempFields1, _c0t__tmp_218, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
      int _c0t__tmp_222;
      struct _c0_Node* _c0t__tmp_219 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      if ((_c0t__tmp_219 != NULL)) {
        struct _c0_Node* _c0t__tmp_220 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        int _c0t__tmp_221 = (cc0_deref(struct _c0_Node, _c0t__tmp_220))._c0__id;
        _c0t__tmp_222 = _c0t__tmp_221;
      } else {
        _c0t__tmp_222 = -(1);
      }
      _c0_addAccEnsureSeparate(_c0v__tempFields1, _c0t__tmp_222, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
    }
    bool _c0t__tmp_224;
    if (!((_c0v_head == NULL))) {
      struct _c0_Node* _c0t__tmp_223 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
      _c0t__tmp_224 = (_c0t__tmp_223 == NULL);
    } else {
      _c0t__tmp_224 = false;
    }
    _c0v__cond_2 = _c0t__tmp_224;
    bool _c0t__tmp_232;
    bool _c0t__tmp_230;
    bool _c0t__tmp_226;
    if (!((_c0v_curr == NULL))) {
      struct _c0_Node* _c0t__tmp_225 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      _c0t__tmp_226 = !((_c0t__tmp_225 == NULL));
    } else {
      _c0t__tmp_226 = false;
    }
    if ((_c0t__tmp_226 && !((_c0v_curr == NULL)))) {
      struct _c0_Node* _c0t__tmp_228 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      struct _c0_Node* _c0t__tmp_229 = (cc0_deref(struct _c0_Node, _c0t__tmp_228))._c0_next;
      _c0t__tmp_230 = !((_c0t__tmp_229 == NULL));
    } else {
      _c0t__tmp_230 = false;
    }
    if (_c0t__tmp_230) {
      struct _c0_Node* _c0t__tmp_231 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      _c0t__tmp_232 = !((_c0t__tmp_231 == NULL));
    } else {
      _c0t__tmp_232 = false;
    }
    _c0v__cond_3 = _c0t__tmp_232;
    bool _c0t__tmp_234;
    if (!((_c0v_curr == NULL))) {
      struct _c0_Node* _c0t__tmp_233 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      _c0t__tmp_234 = (_c0t__tmp_233 == NULL);
    } else {
      _c0t__tmp_234 = false;
    }
    _c0v__cond_5 = _c0t__tmp_234;
    while (true) {
      bool _c0t__tmp_238;
      struct _c0_Node* _c0t__tmp_235 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      if ((_c0t__tmp_235 != NULL)) {
        struct _c0_Node* _c0t__tmp_236 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        struct _c0_Node* _c0t__tmp_237 = (cc0_deref(struct _c0_Node, _c0t__tmp_236))._c0_next;
        _c0t__tmp_238 = (_c0t__tmp_237 != NULL);
      } else {
        _c0t__tmp_238 = false;
      }
      if (_c0t__tmp_238) {
      } else {
        break;
      }
      _c0v_prev = _c0v_curr;
      struct _c0_Node* _c0t__tmp_239 = (cc0_deref(struct _c0_Node, _c0v_prev))._c0_next;
      _c0v_curr = _c0t__tmp_239;
      _c0v__cond_4 = (_c0v_head == _c0v_prev);
      if ((_c0v_head == _c0v_prev)) {
      } else {
        if (((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)) || (((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) || (((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) || (((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4)))) {
          int _c0t__tmp_256;
          if ((_c0v_head != NULL)) {
            int _c0t__tmp_255 = (cc0_deref(struct _c0_Node, _c0v_head))._c0__id;
            _c0t__tmp_256 = _c0t__tmp_255;
          } else {
            _c0t__tmp_256 = -(1);
          }
          _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_256, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
        }
        struct _c0_Node* _c0t__tmp_257 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
        _c0_appendLemmaLoopBody(_c0t__tmp_257, _c0v_prev, _c0v_curr, _c0v__ownedFields);
      }
      int* _c0t__tmp_258 = (cc0_deref(struct _c0_OwnedFields, _c0v__ownedFields))._c0_instanceCounter;
      struct _c0_OwnedFields* _c0t__tmp_259 = _c0_initOwnedFields(_c0t__tmp_258);
      _c0v__tempFields = _c0t__tmp_259;
      bool _c0t__tmp_378;
      bool _c0t__tmp_372;
      bool _c0t__tmp_366;
      bool _c0t__tmp_360;
      bool _c0t__tmp_346;
      bool _c0t__tmp_340;
      bool _c0t__tmp_334;
      bool _c0t__tmp_328;
      bool _c0t__tmp_314;
      bool _c0t__tmp_308;
      bool _c0t__tmp_302;
      bool _c0t__tmp_296;
      bool _c0t__tmp_282;
      bool _c0t__tmp_276;
      bool _c0t__tmp_270;
      bool _c0t__tmp_264;
      if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
        struct _c0_Node* _c0t__tmp_263 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        _c0t__tmp_264 = !((_c0t__tmp_263 == NULL));
      } else {
        _c0t__tmp_264 = false;
      }
      if (_c0t__tmp_264) {
        _c0t__tmp_270 = true;
      } else {
        bool _c0t__tmp_269;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_268 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_269 = !((_c0t__tmp_268 == NULL));
        } else {
          _c0t__tmp_269 = false;
        }
        _c0t__tmp_270 = _c0t__tmp_269;
      }
      if (_c0t__tmp_270) {
        _c0t__tmp_276 = true;
      } else {
        bool _c0t__tmp_275;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_274 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_275 = !((_c0t__tmp_274 == NULL));
        } else {
          _c0t__tmp_275 = false;
        }
        _c0t__tmp_276 = _c0t__tmp_275;
      }
      if (_c0t__tmp_276) {
        _c0t__tmp_282 = true;
      } else {
        bool _c0t__tmp_281;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_280 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_281 = (_c0t__tmp_280 == NULL);
        } else {
          _c0t__tmp_281 = false;
        }
        _c0t__tmp_282 = _c0t__tmp_281;
      }
      if (((_c0t__tmp_282 || (((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) || (((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)))) {
        _c0t__tmp_296 = true;
      } else {
        bool _c0t__tmp_295;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_294 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_295 = !((_c0t__tmp_294 == NULL));
        } else {
          _c0t__tmp_295 = false;
        }
        _c0t__tmp_296 = _c0t__tmp_295;
      }
      if (_c0t__tmp_296) {
        _c0t__tmp_302 = true;
      } else {
        bool _c0t__tmp_301;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_300 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_301 = !((_c0t__tmp_300 == NULL));
        } else {
          _c0t__tmp_301 = false;
        }
        _c0t__tmp_302 = _c0t__tmp_301;
      }
      if (_c0t__tmp_302) {
        _c0t__tmp_308 = true;
      } else {
        bool _c0t__tmp_307;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_306 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_307 = !((_c0t__tmp_306 == NULL));
        } else {
          _c0t__tmp_307 = false;
        }
        _c0t__tmp_308 = _c0t__tmp_307;
      }
      if (_c0t__tmp_308) {
        _c0t__tmp_314 = true;
      } else {
        bool _c0t__tmp_313;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_312 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_313 = (_c0t__tmp_312 == NULL);
        } else {
          _c0t__tmp_313 = false;
        }
        _c0t__tmp_314 = _c0t__tmp_313;
      }
      if (((_c0t__tmp_314 || (((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) || (((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)))) {
        _c0t__tmp_328 = true;
      } else {
        bool _c0t__tmp_327;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_326 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_327 = !((_c0t__tmp_326 == NULL));
        } else {
          _c0t__tmp_327 = false;
        }
        _c0t__tmp_328 = _c0t__tmp_327;
      }
      if (_c0t__tmp_328) {
        _c0t__tmp_334 = true;
      } else {
        bool _c0t__tmp_333;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_332 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_333 = !((_c0t__tmp_332 == NULL));
        } else {
          _c0t__tmp_333 = false;
        }
        _c0t__tmp_334 = _c0t__tmp_333;
      }
      if (_c0t__tmp_334) {
        _c0t__tmp_340 = true;
      } else {
        bool _c0t__tmp_339;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_338 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_339 = !((_c0t__tmp_338 == NULL));
        } else {
          _c0t__tmp_339 = false;
        }
        _c0t__tmp_340 = _c0t__tmp_339;
      }
      if (_c0t__tmp_340) {
        _c0t__tmp_346 = true;
      } else {
        bool _c0t__tmp_345;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_344 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_345 = (_c0t__tmp_344 == NULL);
        } else {
          _c0t__tmp_345 = false;
        }
        _c0t__tmp_346 = _c0t__tmp_345;
      }
      if (((_c0t__tmp_346 || (((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) || (((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4)))) {
        _c0t__tmp_360 = true;
      } else {
        bool _c0t__tmp_359;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_358 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_359 = !((_c0t__tmp_358 == NULL));
        } else {
          _c0t__tmp_359 = false;
        }
        _c0t__tmp_360 = _c0t__tmp_359;
      }
      if (_c0t__tmp_360) {
        _c0t__tmp_366 = true;
      } else {
        bool _c0t__tmp_365;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_364 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_365 = !((_c0t__tmp_364 == NULL));
        } else {
          _c0t__tmp_365 = false;
        }
        _c0t__tmp_366 = _c0t__tmp_365;
      }
      if (_c0t__tmp_366) {
        _c0t__tmp_372 = true;
      } else {
        bool _c0t__tmp_371;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_370 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_371 = !((_c0t__tmp_370 == NULL));
        } else {
          _c0t__tmp_371 = false;
        }
        _c0t__tmp_372 = _c0t__tmp_371;
      }
      if (_c0t__tmp_372) {
        _c0t__tmp_378 = true;
      } else {
        bool _c0t__tmp_377;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_376 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_377 = (_c0t__tmp_376 == NULL);
        } else {
          _c0t__tmp_377 = false;
        }
        _c0t__tmp_378 = _c0t__tmp_377;
      }
      if (((_c0t__tmp_378 || (((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) || (((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4)))) {
        int _c0t__tmp_388;
        if ((_c0v_curr != NULL)) {
          int _c0t__tmp_387 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
          _c0t__tmp_388 = _c0t__tmp_387;
        } else {
          _c0t__tmp_388 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_388, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
      }
      if (((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4)) || (((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) || (((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) || (((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4)))) {
        int _c0t__tmp_405;
        if ((_c0v_curr != NULL)) {
          int _c0t__tmp_404 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
          _c0t__tmp_405 = _c0t__tmp_404;
        } else {
          _c0t__tmp_405 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_405, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
      }
      bool _c0t__tmp_620;
      bool _c0t__tmp_613;
      bool _c0t__tmp_606;
      bool _c0t__tmp_600;
      bool _c0t__tmp_593;
      bool _c0t__tmp_586;
      bool _c0t__tmp_580;
      bool _c0t__tmp_573;
      bool _c0t__tmp_566;
      bool _c0t__tmp_559;
      bool _c0t__tmp_552;
      bool _c0t__tmp_546;
      bool _c0t__tmp_539;
      bool _c0t__tmp_532;
      bool _c0t__tmp_526;
      bool _c0t__tmp_519;
      bool _c0t__tmp_512;
      bool _c0t__tmp_505;
      bool _c0t__tmp_498;
      bool _c0t__tmp_492;
      bool _c0t__tmp_485;
      bool _c0t__tmp_478;
      bool _c0t__tmp_472;
      bool _c0t__tmp_465;
      bool _c0t__tmp_458;
      bool _c0t__tmp_451;
      bool _c0t__tmp_444;
      bool _c0t__tmp_438;
      bool _c0t__tmp_431;
      bool _c0t__tmp_424;
      bool _c0t__tmp_418;
      bool _c0t__tmp_410;
      if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4)) {
        struct _c0_Node* _c0t__tmp_409 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        _c0t__tmp_410 = !((_c0t__tmp_409 == NULL));
      } else {
        _c0t__tmp_410 = false;
      }
      if ((_c0t__tmp_410 && !(_c0v__cond_5))) {
        _c0t__tmp_418 = true;
      } else {
        bool _c0t__tmp_416;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_415 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_416 = !((_c0t__tmp_415 == NULL));
        } else {
          _c0t__tmp_416 = false;
        }
        _c0t__tmp_418 = (_c0t__tmp_416 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_418) {
        _c0t__tmp_424 = true;
      } else {
        bool _c0t__tmp_423;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_422 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_423 = !((_c0t__tmp_422 == NULL));
        } else {
          _c0t__tmp_423 = false;
        }
        _c0t__tmp_424 = _c0t__tmp_423;
      }
      if (_c0t__tmp_424) {
        _c0t__tmp_431 = true;
      } else {
        bool _c0t__tmp_429;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_428 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_429 = !((_c0t__tmp_428 == NULL));
        } else {
          _c0t__tmp_429 = false;
        }
        _c0t__tmp_431 = (_c0t__tmp_429 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_431) {
        _c0t__tmp_438 = true;
      } else {
        bool _c0t__tmp_436;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_435 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_436 = !((_c0t__tmp_435 == NULL));
        } else {
          _c0t__tmp_436 = false;
        }
        _c0t__tmp_438 = (_c0t__tmp_436 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_438) {
        _c0t__tmp_444 = true;
      } else {
        bool _c0t__tmp_443;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_442 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_443 = !((_c0t__tmp_442 == NULL));
        } else {
          _c0t__tmp_443 = false;
        }
        _c0t__tmp_444 = _c0t__tmp_443;
      }
      if (_c0t__tmp_444) {
        _c0t__tmp_451 = true;
      } else {
        bool _c0t__tmp_449;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_448 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_449 = (_c0t__tmp_448 == NULL);
        } else {
          _c0t__tmp_449 = false;
        }
        _c0t__tmp_451 = (_c0t__tmp_449 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_451) {
        _c0t__tmp_458 = true;
      } else {
        bool _c0t__tmp_456;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_455 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_456 = (_c0t__tmp_455 == NULL);
        } else {
          _c0t__tmp_456 = false;
        }
        _c0t__tmp_458 = (_c0t__tmp_456 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_458) {
        _c0t__tmp_465 = true;
      } else {
        bool _c0t__tmp_463;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_462 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_463 = !((_c0t__tmp_462 == NULL));
        } else {
          _c0t__tmp_463 = false;
        }
        _c0t__tmp_465 = (_c0t__tmp_463 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_465) {
        _c0t__tmp_472 = true;
      } else {
        bool _c0t__tmp_470;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_469 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_470 = !((_c0t__tmp_469 == NULL));
        } else {
          _c0t__tmp_470 = false;
        }
        _c0t__tmp_472 = (_c0t__tmp_470 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_472) {
        _c0t__tmp_478 = true;
      } else {
        bool _c0t__tmp_477;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_476 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_477 = !((_c0t__tmp_476 == NULL));
        } else {
          _c0t__tmp_477 = false;
        }
        _c0t__tmp_478 = _c0t__tmp_477;
      }
      if (_c0t__tmp_478) {
        _c0t__tmp_485 = true;
      } else {
        bool _c0t__tmp_483;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_482 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_483 = !((_c0t__tmp_482 == NULL));
        } else {
          _c0t__tmp_483 = false;
        }
        _c0t__tmp_485 = (_c0t__tmp_483 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_485) {
        _c0t__tmp_492 = true;
      } else {
        bool _c0t__tmp_490;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_489 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_490 = !((_c0t__tmp_489 == NULL));
        } else {
          _c0t__tmp_490 = false;
        }
        _c0t__tmp_492 = (_c0t__tmp_490 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_492) {
        _c0t__tmp_498 = true;
      } else {
        bool _c0t__tmp_497;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_496 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_497 = !((_c0t__tmp_496 == NULL));
        } else {
          _c0t__tmp_497 = false;
        }
        _c0t__tmp_498 = _c0t__tmp_497;
      }
      if (_c0t__tmp_498) {
        _c0t__tmp_505 = true;
      } else {
        bool _c0t__tmp_503;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_502 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_503 = (_c0t__tmp_502 == NULL);
        } else {
          _c0t__tmp_503 = false;
        }
        _c0t__tmp_505 = (_c0t__tmp_503 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_505) {
        _c0t__tmp_512 = true;
      } else {
        bool _c0t__tmp_510;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_509 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_510 = (_c0t__tmp_509 == NULL);
        } else {
          _c0t__tmp_510 = false;
        }
        _c0t__tmp_512 = (_c0t__tmp_510 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_512) {
        _c0t__tmp_519 = true;
      } else {
        bool _c0t__tmp_517;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_516 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_517 = !((_c0t__tmp_516 == NULL));
        } else {
          _c0t__tmp_517 = false;
        }
        _c0t__tmp_519 = (_c0t__tmp_517 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_519) {
        _c0t__tmp_526 = true;
      } else {
        bool _c0t__tmp_524;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_523 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_524 = !((_c0t__tmp_523 == NULL));
        } else {
          _c0t__tmp_524 = false;
        }
        _c0t__tmp_526 = (_c0t__tmp_524 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_526) {
        _c0t__tmp_532 = true;
      } else {
        bool _c0t__tmp_531;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_530 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_531 = !((_c0t__tmp_530 == NULL));
        } else {
          _c0t__tmp_531 = false;
        }
        _c0t__tmp_532 = _c0t__tmp_531;
      }
      if (_c0t__tmp_532) {
        _c0t__tmp_539 = true;
      } else {
        bool _c0t__tmp_537;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_536 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_537 = !((_c0t__tmp_536 == NULL));
        } else {
          _c0t__tmp_537 = false;
        }
        _c0t__tmp_539 = (_c0t__tmp_537 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_539) {
        _c0t__tmp_546 = true;
      } else {
        bool _c0t__tmp_544;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_543 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_544 = !((_c0t__tmp_543 == NULL));
        } else {
          _c0t__tmp_544 = false;
        }
        _c0t__tmp_546 = (_c0t__tmp_544 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_546) {
        _c0t__tmp_552 = true;
      } else {
        bool _c0t__tmp_551;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_550 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_551 = !((_c0t__tmp_550 == NULL));
        } else {
          _c0t__tmp_551 = false;
        }
        _c0t__tmp_552 = _c0t__tmp_551;
      }
      if (_c0t__tmp_552) {
        _c0t__tmp_559 = true;
      } else {
        bool _c0t__tmp_557;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_556 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_557 = (_c0t__tmp_556 == NULL);
        } else {
          _c0t__tmp_557 = false;
        }
        _c0t__tmp_559 = (_c0t__tmp_557 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_559) {
        _c0t__tmp_566 = true;
      } else {
        bool _c0t__tmp_564;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_563 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_564 = (_c0t__tmp_563 == NULL);
        } else {
          _c0t__tmp_564 = false;
        }
        _c0t__tmp_566 = (_c0t__tmp_564 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_566) {
        _c0t__tmp_573 = true;
      } else {
        bool _c0t__tmp_571;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_570 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_571 = !((_c0t__tmp_570 == NULL));
        } else {
          _c0t__tmp_571 = false;
        }
        _c0t__tmp_573 = (_c0t__tmp_571 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_573) {
        _c0t__tmp_580 = true;
      } else {
        bool _c0t__tmp_578;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_577 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_578 = !((_c0t__tmp_577 == NULL));
        } else {
          _c0t__tmp_578 = false;
        }
        _c0t__tmp_580 = (_c0t__tmp_578 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_580) {
        _c0t__tmp_586 = true;
      } else {
        bool _c0t__tmp_585;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_584 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_585 = !((_c0t__tmp_584 == NULL));
        } else {
          _c0t__tmp_585 = false;
        }
        _c0t__tmp_586 = _c0t__tmp_585;
      }
      if (_c0t__tmp_586) {
        _c0t__tmp_593 = true;
      } else {
        bool _c0t__tmp_591;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_590 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_591 = !((_c0t__tmp_590 == NULL));
        } else {
          _c0t__tmp_591 = false;
        }
        _c0t__tmp_593 = (_c0t__tmp_591 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_593) {
        _c0t__tmp_600 = true;
      } else {
        bool _c0t__tmp_598;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_597 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_598 = !((_c0t__tmp_597 == NULL));
        } else {
          _c0t__tmp_598 = false;
        }
        _c0t__tmp_600 = (_c0t__tmp_598 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_600) {
        _c0t__tmp_606 = true;
      } else {
        bool _c0t__tmp_605;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_604 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_605 = !((_c0t__tmp_604 == NULL));
        } else {
          _c0t__tmp_605 = false;
        }
        _c0t__tmp_606 = _c0t__tmp_605;
      }
      if (_c0t__tmp_606) {
        _c0t__tmp_613 = true;
      } else {
        bool _c0t__tmp_611;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_610 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_611 = (_c0t__tmp_610 == NULL);
        } else {
          _c0t__tmp_611 = false;
        }
        _c0t__tmp_613 = (_c0t__tmp_611 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_613) {
        _c0t__tmp_620 = true;
      } else {
        bool _c0t__tmp_618;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_617 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_618 = (_c0t__tmp_617 == NULL);
        } else {
          _c0t__tmp_618 = false;
        }
        _c0t__tmp_620 = (_c0t__tmp_618 && !(_c0v__cond_5));
      }
      if (_c0t__tmp_620) {
        int _c0t__tmp_624;
        struct _c0_Node* _c0t__tmp_621 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        if ((_c0t__tmp_621 != NULL)) {
          struct _c0_Node* _c0t__tmp_622 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          int _c0t__tmp_623 = (cc0_deref(struct _c0_Node, _c0t__tmp_622))._c0__id;
          _c0t__tmp_624 = _c0t__tmp_623;
        } else {
          _c0t__tmp_624 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_624, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
      }
      bool _c0t__tmp_671;
      bool _c0t__tmp_665;
      bool _c0t__tmp_659;
      bool _c0t__tmp_653;
      bool _c0t__tmp_647;
      bool _c0t__tmp_641;
      bool _c0t__tmp_635;
      bool _c0t__tmp_629;
      if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4)) {
        struct _c0_Node* _c0t__tmp_628 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        _c0t__tmp_629 = !((_c0t__tmp_628 == NULL));
      } else {
        _c0t__tmp_629 = false;
      }
      if (_c0t__tmp_629) {
        _c0t__tmp_635 = true;
      } else {
        bool _c0t__tmp_634;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_633 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_634 = !((_c0t__tmp_633 == NULL));
        } else {
          _c0t__tmp_634 = false;
        }
        _c0t__tmp_635 = _c0t__tmp_634;
      }
      if (_c0t__tmp_635) {
        _c0t__tmp_641 = true;
      } else {
        bool _c0t__tmp_640;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_639 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_640 = !((_c0t__tmp_639 == NULL));
        } else {
          _c0t__tmp_640 = false;
        }
        _c0t__tmp_641 = _c0t__tmp_640;
      }
      if (_c0t__tmp_641) {
        _c0t__tmp_647 = true;
      } else {
        bool _c0t__tmp_646;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_645 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_646 = !((_c0t__tmp_645 == NULL));
        } else {
          _c0t__tmp_646 = false;
        }
        _c0t__tmp_647 = _c0t__tmp_646;
      }
      if (_c0t__tmp_647) {
        _c0t__tmp_653 = true;
      } else {
        bool _c0t__tmp_652;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_651 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_652 = !((_c0t__tmp_651 == NULL));
        } else {
          _c0t__tmp_652 = false;
        }
        _c0t__tmp_653 = _c0t__tmp_652;
      }
      if (_c0t__tmp_653) {
        _c0t__tmp_659 = true;
      } else {
        bool _c0t__tmp_658;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_657 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_658 = !((_c0t__tmp_657 == NULL));
        } else {
          _c0t__tmp_658 = false;
        }
        _c0t__tmp_659 = _c0t__tmp_658;
      }
      if (_c0t__tmp_659) {
        _c0t__tmp_665 = true;
      } else {
        bool _c0t__tmp_664;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_663 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_664 = !((_c0t__tmp_663 == NULL));
        } else {
          _c0t__tmp_664 = false;
        }
        _c0t__tmp_665 = _c0t__tmp_664;
      }
      if (_c0t__tmp_665) {
        _c0t__tmp_671 = true;
      } else {
        bool _c0t__tmp_670;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_669 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_670 = !((_c0t__tmp_669 == NULL));
        } else {
          _c0t__tmp_670 = false;
        }
        _c0t__tmp_671 = _c0t__tmp_670;
      }
      if (_c0t__tmp_671) {
        int _c0t__tmp_675;
        struct _c0_Node* _c0t__tmp_672 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        if ((_c0t__tmp_672 != NULL)) {
          struct _c0_Node* _c0t__tmp_673 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          int _c0t__tmp_674 = (cc0_deref(struct _c0_Node, _c0t__tmp_673))._c0__id;
          _c0t__tmp_675 = _c0t__tmp_674;
        } else {
          _c0t__tmp_675 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_675, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
      }
      bool _c0t__tmp_698;
      bool _c0t__tmp_692;
      bool _c0t__tmp_686;
      bool _c0t__tmp_680;
      if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4)) {
        struct _c0_Node* _c0t__tmp_679 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        _c0t__tmp_680 = !((_c0t__tmp_679 == NULL));
      } else {
        _c0t__tmp_680 = false;
      }
      if (_c0t__tmp_680) {
        _c0t__tmp_686 = true;
      } else {
        bool _c0t__tmp_685;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_684 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_685 = !((_c0t__tmp_684 == NULL));
        } else {
          _c0t__tmp_685 = false;
        }
        _c0t__tmp_686 = _c0t__tmp_685;
      }
      if (_c0t__tmp_686) {
        _c0t__tmp_692 = true;
      } else {
        bool _c0t__tmp_691;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_690 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_691 = !((_c0t__tmp_690 == NULL));
        } else {
          _c0t__tmp_691 = false;
        }
        _c0t__tmp_692 = _c0t__tmp_691;
      }
      if (_c0t__tmp_692) {
        _c0t__tmp_698 = true;
      } else {
        bool _c0t__tmp_697;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && _c0v__cond_4)) {
          struct _c0_Node* _c0t__tmp_696 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_697 = !((_c0t__tmp_696 == NULL));
        } else {
          _c0t__tmp_697 = false;
        }
        _c0t__tmp_698 = _c0t__tmp_697;
      }
      if (_c0t__tmp_698) {
        bool _c0t__tmp_703;
        struct _c0_Node* _c0t__tmp_699 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
        struct _c0_Node* _c0t__tmp_700 = (cc0_deref(struct _c0_Node, _c0t__tmp_699))._c0_next;
        struct _c0_Node* _c0t__tmp_701 = (cc0_deref(struct _c0_Node, _c0t__tmp_700))._c0_next;
        if (!((_c0t__tmp_701 == NULL))) {
          struct _c0_Node* _c0t__tmp_702 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_703 = !((_c0t__tmp_702 == NULL));
        } else {
          _c0t__tmp_703 = false;
        }
        bool _c0t__tmp_708;
        struct _c0_Node* _c0t__tmp_704 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
        struct _c0_Node* _c0t__tmp_705 = (cc0_deref(struct _c0_Node, _c0t__tmp_704))._c0_next;
        struct _c0_Node* _c0t__tmp_706 = (cc0_deref(struct _c0_Node, _c0t__tmp_705))._c0_next;
        if (!((_c0t__tmp_706 == NULL))) {
          struct _c0_Node* _c0t__tmp_707 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_708 = !((_c0t__tmp_707 == NULL));
        } else {
          _c0t__tmp_708 = false;
        }
        cc0_assert((_c0t__tmp_703 == _c0t__tmp_708), c0_string_fromliteral("src/test/resources/runtime-analysis/stack.verified.c0: 240.9-240.142: assert failed"));
      }
      bool _c0t__tmp_755;
      bool _c0t__tmp_749;
      bool _c0t__tmp_743;
      bool _c0t__tmp_737;
      bool _c0t__tmp_731;
      bool _c0t__tmp_725;
      bool _c0t__tmp_719;
      bool _c0t__tmp_713;
      if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
        struct _c0_Node* _c0t__tmp_712 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        _c0t__tmp_713 = !((_c0t__tmp_712 == NULL));
      } else {
        _c0t__tmp_713 = false;
      }
      if (_c0t__tmp_713) {
        _c0t__tmp_719 = true;
      } else {
        bool _c0t__tmp_718;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_717 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_718 = !((_c0t__tmp_717 == NULL));
        } else {
          _c0t__tmp_718 = false;
        }
        _c0t__tmp_719 = _c0t__tmp_718;
      }
      if (_c0t__tmp_719) {
        _c0t__tmp_725 = true;
      } else {
        bool _c0t__tmp_724;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_723 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_724 = !((_c0t__tmp_723 == NULL));
        } else {
          _c0t__tmp_724 = false;
        }
        _c0t__tmp_725 = _c0t__tmp_724;
      }
      if (_c0t__tmp_725) {
        _c0t__tmp_731 = true;
      } else {
        bool _c0t__tmp_730;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_729 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_730 = !((_c0t__tmp_729 == NULL));
        } else {
          _c0t__tmp_730 = false;
        }
        _c0t__tmp_731 = _c0t__tmp_730;
      }
      if (_c0t__tmp_731) {
        _c0t__tmp_737 = true;
      } else {
        bool _c0t__tmp_736;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_735 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_736 = !((_c0t__tmp_735 == NULL));
        } else {
          _c0t__tmp_736 = false;
        }
        _c0t__tmp_737 = _c0t__tmp_736;
      }
      if (_c0t__tmp_737) {
        _c0t__tmp_743 = true;
      } else {
        bool _c0t__tmp_742;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_741 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_742 = !((_c0t__tmp_741 == NULL));
        } else {
          _c0t__tmp_742 = false;
        }
        _c0t__tmp_743 = _c0t__tmp_742;
      }
      if (_c0t__tmp_743) {
        _c0t__tmp_749 = true;
      } else {
        bool _c0t__tmp_748;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_747 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_748 = !((_c0t__tmp_747 == NULL));
        } else {
          _c0t__tmp_748 = false;
        }
        _c0t__tmp_749 = _c0t__tmp_748;
      }
      if (_c0t__tmp_749) {
        _c0t__tmp_755 = true;
      } else {
        bool _c0t__tmp_754;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_753 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_754 = !((_c0t__tmp_753 == NULL));
        } else {
          _c0t__tmp_754 = false;
        }
        _c0t__tmp_755 = _c0t__tmp_754;
      }
      if (_c0t__tmp_755) {
        struct _c0_Node* _c0t__tmp_756 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        cc0_assert(!((_c0t__tmp_756 == NULL)), c0_string_fromliteral("src/test/resources/runtime-analysis/stack.verified.c0: 244.9-244.39: assert failed"));
      }
      bool _c0t__tmp_803;
      bool _c0t__tmp_797;
      bool _c0t__tmp_791;
      bool _c0t__tmp_785;
      bool _c0t__tmp_779;
      bool _c0t__tmp_773;
      bool _c0t__tmp_767;
      bool _c0t__tmp_761;
      if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
        struct _c0_Node* _c0t__tmp_760 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        _c0t__tmp_761 = !((_c0t__tmp_760 == NULL));
      } else {
        _c0t__tmp_761 = false;
      }
      if (_c0t__tmp_761) {
        _c0t__tmp_767 = true;
      } else {
        bool _c0t__tmp_766;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_765 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_766 = (_c0t__tmp_765 == NULL);
        } else {
          _c0t__tmp_766 = false;
        }
        _c0t__tmp_767 = _c0t__tmp_766;
      }
      if (_c0t__tmp_767) {
        _c0t__tmp_773 = true;
      } else {
        bool _c0t__tmp_772;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_771 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_772 = !((_c0t__tmp_771 == NULL));
        } else {
          _c0t__tmp_772 = false;
        }
        _c0t__tmp_773 = _c0t__tmp_772;
      }
      if (_c0t__tmp_773) {
        _c0t__tmp_779 = true;
      } else {
        bool _c0t__tmp_778;
        if ((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_777 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_778 = (_c0t__tmp_777 == NULL);
        } else {
          _c0t__tmp_778 = false;
        }
        _c0t__tmp_779 = _c0t__tmp_778;
      }
      if (_c0t__tmp_779) {
        _c0t__tmp_785 = true;
      } else {
        bool _c0t__tmp_784;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_783 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_784 = !((_c0t__tmp_783 == NULL));
        } else {
          _c0t__tmp_784 = false;
        }
        _c0t__tmp_785 = _c0t__tmp_784;
      }
      if (_c0t__tmp_785) {
        _c0t__tmp_791 = true;
      } else {
        bool _c0t__tmp_790;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_789 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_790 = (_c0t__tmp_789 == NULL);
        } else {
          _c0t__tmp_790 = false;
        }
        _c0t__tmp_791 = _c0t__tmp_790;
      }
      if (_c0t__tmp_791) {
        _c0t__tmp_797 = true;
      } else {
        bool _c0t__tmp_796;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_795 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_796 = !((_c0t__tmp_795 == NULL));
        } else {
          _c0t__tmp_796 = false;
        }
        _c0t__tmp_797 = _c0t__tmp_796;
      }
      if (_c0t__tmp_797) {
        _c0t__tmp_803 = true;
      } else {
        bool _c0t__tmp_802;
        if ((((!(_c0v__cond_1) && _c0v__cond_2) && _c0v__cond_3) && !(_c0v__cond_4))) {
          struct _c0_Node* _c0t__tmp_801 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_802 = (_c0t__tmp_801 == NULL);
        } else {
          _c0t__tmp_802 = false;
        }
        _c0t__tmp_803 = _c0t__tmp_802;
      }
      if (_c0t__tmp_803) {
        bool _c0t__tmp_807;
        struct _c0_Node* _c0t__tmp_804 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        struct _c0_Node* _c0t__tmp_805 = (cc0_deref(struct _c0_Node, _c0t__tmp_804))._c0_next;
        if (!((_c0t__tmp_805 == NULL))) {
          struct _c0_Node* _c0t__tmp_806 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_807 = !((_c0t__tmp_806 == NULL));
        } else {
          _c0t__tmp_807 = false;
        }
        bool _c0t__tmp_811;
        struct _c0_Node* _c0t__tmp_808 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        struct _c0_Node* _c0t__tmp_809 = (cc0_deref(struct _c0_Node, _c0t__tmp_808))._c0_next;
        if (!((_c0t__tmp_809 == NULL))) {
          struct _c0_Node* _c0t__tmp_810 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_811 = !((_c0t__tmp_810 == NULL));
        } else {
          _c0t__tmp_811 = false;
        }
        cc0_assert((_c0t__tmp_807 == _c0t__tmp_811), c0_string_fromliteral("src/test/resources/runtime-analysis/stack.verified.c0: 248.9-248.130: assert failed"));
      }
      int _c0t__tmp_813;
      if ((_c0v_curr != NULL)) {
        int _c0t__tmp_812 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
        _c0t__tmp_813 = _c0t__tmp_812;
      } else {
        _c0t__tmp_813 = -(1);
      }
      _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_813, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
      int _c0t__tmp_815;
      if ((_c0v_curr != NULL)) {
        int _c0t__tmp_814 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
        _c0t__tmp_815 = _c0t__tmp_814;
      } else {
        _c0t__tmp_815 = -(1);
      }
      _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_815, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
      struct _c0_Node* _c0t__tmp_816 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      if (!((_c0t__tmp_816 == NULL))) {
        int _c0t__tmp_820;
        struct _c0_Node* _c0t__tmp_817 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        if ((_c0t__tmp_817 != NULL)) {
          struct _c0_Node* _c0t__tmp_818 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          int _c0t__tmp_819 = (cc0_deref(struct _c0_Node, _c0t__tmp_818))._c0__id;
          _c0t__tmp_820 = _c0t__tmp_819;
        } else {
          _c0t__tmp_820 = -(1);
        }
        _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_820, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
        int _c0t__tmp_824;
        struct _c0_Node* _c0t__tmp_821 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        if ((_c0t__tmp_821 != NULL)) {
          struct _c0_Node* _c0t__tmp_822 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          int _c0t__tmp_823 = (cc0_deref(struct _c0_Node, _c0t__tmp_822))._c0__id;
          _c0t__tmp_824 = _c0t__tmp_823;
        } else {
          _c0t__tmp_824 = -(1);
        }
        _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_824, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
      }
    }
    struct _c0_Node** _c0t__tmp_825;
    _c0t__tmp_825 = &((cc0_deref(struct _c0_Node, _c0v_curr))._c0_next);
    cc0_deref(struct _c0_Node*, _c0t__tmp_825) = NULL;
    return 1;
  }
}

struct _c0_Node;
struct _c0_OwnedFields;
struct _c0_Node* _c0_push(struct _c0_Node* _c0v_head, int _c0v_val, struct _c0_OwnedFields* _c0v__ownedFields) {
  struct _c0_Node* _c0v_n = NULL;
  struct _c0_Node* _c0v_curr = NULL;
  struct _c0_Node* _c0v_tmp = NULL;
  struct _c0_Node* _c0v_prev = NULL;
  bool _c0v__cond_1 = false;
  bool _c0v__cond_2 = false;
  bool _c0v__cond_3 = false;
  bool _c0v__cond_4 = false;
  bool _c0v__cond_5 = false;
  bool _c0v__cond_6 = false;
  bool _c0v__cond_7 = false;
  bool _c0v__cond_8 = false;
  bool _c0v__cond_9 = false;
  bool _c0v__cond_10 = false;
  bool _c0v__cond_11 = false;
  struct _c0_OwnedFields* _c0v__tempFields = NULL;
  struct _c0_Node* _c0v__ = NULL;
  _c0_add_seg(_c0v_head, _c0v__ownedFields);
  _c0v__cond_1 = (_c0v_head == NULL);
  _c0v__cond_2 = (_c0v_head == NULL);
  if ((_c0v_head == NULL)) {
    struct _c0_Node* _c0t__tmp_826 = cc0_alloc(struct _c0_Node);
    _c0v_n = _c0t__tmp_826;
    int* _c0t__tmp_827;
    _c0t__tmp_827 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0__id);
    int _c0t__tmp_828 = _c0_addStructAcc(_c0v__ownedFields, 3);
    cc0_deref(int, _c0t__tmp_827) = _c0t__tmp_828;
    int* _c0t__tmp_829;
    _c0t__tmp_829 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_val);
    cc0_deref(int, _c0t__tmp_829) = _c0v_val;
    struct _c0_Node** _c0t__tmp_830;
    _c0t__tmp_830 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_next);
    cc0_deref(struct _c0_Node*, _c0t__tmp_830) = _c0v_head;
    return _c0v_n;
  } else {
    _c0v_curr = _c0v_head;
    bool _c0t__tmp_832;
    if (!((_c0v_head == NULL))) {
      struct _c0_Node* _c0t__tmp_831 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
      _c0t__tmp_832 = (_c0t__tmp_831 == NULL);
    } else {
      _c0t__tmp_832 = false;
    }
    _c0v__cond_3 = _c0t__tmp_832;
    _c0v__cond_4 = true;
    bool _c0t__tmp_834;
    if (!((_c0v_head == NULL))) {
      struct _c0_Node* _c0t__tmp_833 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
      _c0t__tmp_834 = (_c0t__tmp_833 == NULL);
    } else {
      _c0t__tmp_834 = false;
    }
    _c0v__cond_5 = _c0t__tmp_834;
    bool _c0t__tmp_836;
    if (!((_c0v_curr == NULL))) {
      struct _c0_Node* _c0t__tmp_835 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      _c0t__tmp_836 = (_c0t__tmp_835 == NULL);
    } else {
      _c0t__tmp_836 = false;
    }
    _c0v__cond_6 = _c0t__tmp_836;
    while (true) {
      struct _c0_Node* _c0t__tmp_837 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      if ((_c0t__tmp_837 != NULL)) {
      } else {
        break;
      }
      _c0v_prev = _c0v_curr;
      struct _c0_Node* _c0t__tmp_838 = (cc0_deref(struct _c0_Node, _c0v_prev))._c0_next;
      _c0v_curr = _c0t__tmp_838;
      _c0v__cond_7 = (_c0v_head == _c0v_prev);
      _c0v__cond_8 = (_c0v_curr == _c0v_curr);
      _c0v__cond_9 = (_c0v_head == _c0v_prev);
      if ((_c0v_head == _c0v_prev)) {
      } else {
        struct _c0_Node* _c0t__tmp_839 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
        _c0_appendLemmaLoopBody(_c0t__tmp_839, _c0v_prev, _c0v_curr, _c0v__ownedFields);
      }
      if (((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr)))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr)))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr))))) {
        int _c0t__tmp_880;
        if ((_c0v_head != NULL)) {
          int _c0t__tmp_879 = (cc0_deref(struct _c0_Node, _c0v_head))._c0__id;
          _c0t__tmp_880 = _c0t__tmp_879;
        } else {
          _c0t__tmp_880 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_880, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
      }
      if (((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr)))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr)))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr)))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr)))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr)))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr)))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr))))) {
        int _c0t__tmp_961;
        if ((_c0v_head != NULL)) {
          int _c0t__tmp_960 = (cc0_deref(struct _c0_Node, _c0v_head))._c0__id;
          _c0t__tmp_961 = _c0t__tmp_960;
        } else {
          _c0t__tmp_961 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_961, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
      }
      if (((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr)))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr)))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !((_c0v_head == _c0v_curr))))) {
        struct _c0_Node* _c0t__tmp_1001 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
        _c0_segHelper(_c0t__tmp_1001, _c0v_curr, _c0v__ownedFields);
      }
      _c0v__cond_10 = (_c0v_head == _c0v_curr);
      if (((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10))) || (((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)))) {
        int _c0t__tmp_1042;
        if ((_c0v_curr != NULL)) {
          int _c0t__tmp_1041 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
          _c0t__tmp_1042 = _c0t__tmp_1041;
        } else {
          _c0t__tmp_1042 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1042, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
      }
      bool _c0t__tmp_1044;
      if (!((_c0v_curr == NULL))) {
        struct _c0_Node* _c0t__tmp_1043 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        _c0t__tmp_1044 = (_c0t__tmp_1043 == NULL);
      } else {
        _c0t__tmp_1044 = false;
      }
      _c0v__cond_11 = _c0t__tmp_1044;
      int* _c0t__tmp_1045 = (cc0_deref(struct _c0_OwnedFields, _c0v__ownedFields))._c0_instanceCounter;
      struct _c0_OwnedFields* _c0t__tmp_1046 = _c0_initOwnedFields(_c0t__tmp_1045);
      _c0v__tempFields = _c0t__tmp_1046;
      if ((((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && _c0v__cond_11)) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11))) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && _c0v__cond_11)) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11))) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && _c0v__cond_11)) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11))) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && _c0v__cond_11))) {
        int _c0t__tmp_1135;
        if ((_c0v_curr != NULL)) {
          int _c0t__tmp_1134 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
          _c0t__tmp_1135 = _c0t__tmp_1134;
        } else {
          _c0t__tmp_1135 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1135, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
      }
      bool _c0t__tmp_1186;
      bool _c0t__tmp_1173;
      bool _c0t__tmp_1160;
      bool _c0t__tmp_1147;
      if (((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11))) {
        struct _c0_Node* _c0t__tmp_1146 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        _c0t__tmp_1147 = !((_c0t__tmp_1146 == NULL));
      } else {
        _c0t__tmp_1147 = false;
      }
      if (_c0t__tmp_1147) {
        _c0t__tmp_1160 = true;
      } else {
        bool _c0t__tmp_1159;
        if (((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11))) {
          struct _c0_Node* _c0t__tmp_1158 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_1159 = !((_c0t__tmp_1158 == NULL));
        } else {
          _c0t__tmp_1159 = false;
        }
        _c0t__tmp_1160 = _c0t__tmp_1159;
      }
      if (_c0t__tmp_1160) {
        _c0t__tmp_1173 = true;
      } else {
        bool _c0t__tmp_1172;
        if (((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11))) {
          struct _c0_Node* _c0t__tmp_1171 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_1172 = !((_c0t__tmp_1171 == NULL));
        } else {
          _c0t__tmp_1172 = false;
        }
        _c0t__tmp_1173 = _c0t__tmp_1172;
      }
      if (_c0t__tmp_1173) {
        _c0t__tmp_1186 = true;
      } else {
        bool _c0t__tmp_1185;
        if (((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11))) {
          struct _c0_Node* _c0t__tmp_1184 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_1185 = !((_c0t__tmp_1184 == NULL));
        } else {
          _c0t__tmp_1185 = false;
        }
        _c0t__tmp_1186 = _c0t__tmp_1185;
      }
      if (_c0t__tmp_1186) {
        int _c0t__tmp_1190;
        struct _c0_Node* _c0t__tmp_1187 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        if ((_c0t__tmp_1187 != NULL)) {
          struct _c0_Node* _c0t__tmp_1188 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          int _c0t__tmp_1189 = (cc0_deref(struct _c0_Node, _c0t__tmp_1188))._c0__id;
          _c0t__tmp_1190 = _c0t__tmp_1189;
        } else {
          _c0t__tmp_1190 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1190, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
        int _c0t__tmp_1194;
        struct _c0_Node* _c0t__tmp_1191 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        if ((_c0t__tmp_1191 != NULL)) {
          struct _c0_Node* _c0t__tmp_1192 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          int _c0t__tmp_1193 = (cc0_deref(struct _c0_Node, _c0t__tmp_1192))._c0__id;
          _c0t__tmp_1194 = _c0t__tmp_1193;
        } else {
          _c0t__tmp_1194 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1194, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
        struct _c0_Node* _c0t__tmp_1195 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        struct _c0_Node* _c0t__tmp_1196 = (cc0_deref(struct _c0_Node, _c0t__tmp_1195))._c0_next;
        _c0_segHelper(_c0t__tmp_1196, NULL, _c0v__ownedFields);
      }
      if ((((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && _c0v__cond_11)) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11))) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && _c0v__cond_11)) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11))) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && _c0v__cond_11)) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11))) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_4) && _c0v__cond_5) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && _c0v__cond_11))) {
        _c0_segHelper(_c0v_head, _c0v_curr, _c0v__ownedFields);
      }
      int _c0t__tmp_1285;
      if ((_c0v_curr != NULL)) {
        int _c0t__tmp_1284 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
        _c0t__tmp_1285 = _c0t__tmp_1284;
      } else {
        _c0t__tmp_1285 = -(1);
      }
      _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_1285, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
      int _c0t__tmp_1287;
      if ((_c0v_curr != NULL)) {
        int _c0t__tmp_1286 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
        _c0t__tmp_1287 = _c0t__tmp_1286;
      } else {
        _c0t__tmp_1287 = -(1);
      }
      _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_1287, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
      _c0_sep_segHelper(_c0v_head, _c0v_curr, _c0v__tempFields);
      struct _c0_Node* _c0t__tmp_1288 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      if (!((_c0t__tmp_1288 == NULL))) {
        int _c0t__tmp_1292;
        struct _c0_Node* _c0t__tmp_1289 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        if ((_c0t__tmp_1289 != NULL)) {
          struct _c0_Node* _c0t__tmp_1290 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          int _c0t__tmp_1291 = (cc0_deref(struct _c0_Node, _c0t__tmp_1290))._c0__id;
          _c0t__tmp_1292 = _c0t__tmp_1291;
        } else {
          _c0t__tmp_1292 = -(1);
        }
        _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_1292, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
        int _c0t__tmp_1296;
        struct _c0_Node* _c0t__tmp_1293 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        if ((_c0t__tmp_1293 != NULL)) {
          struct _c0_Node* _c0t__tmp_1294 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          int _c0t__tmp_1295 = (cc0_deref(struct _c0_Node, _c0t__tmp_1294))._c0__id;
          _c0t__tmp_1296 = _c0t__tmp_1295;
        } else {
          _c0t__tmp_1296 = -(1);
        }
        _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_1296, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
        struct _c0_Node* _c0t__tmp_1297 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        struct _c0_Node* _c0t__tmp_1298 = (cc0_deref(struct _c0_Node, _c0t__tmp_1297))._c0_next;
        _c0_sep_segHelper(_c0t__tmp_1298, NULL, _c0v__tempFields);
      }
    }
    struct _c0_Node* _c0t__tmp_1299 = cc0_alloc(struct _c0_Node);
    _c0v_tmp = _c0t__tmp_1299;
    int* _c0t__tmp_1300;
    _c0t__tmp_1300 = &((cc0_deref(struct _c0_Node, _c0v_tmp))._c0__id);
    int _c0t__tmp_1301 = _c0_addStructAcc(_c0v__ownedFields, 3);
    cc0_deref(int, _c0t__tmp_1300) = _c0t__tmp_1301;
    int* _c0t__tmp_1302;
    _c0t__tmp_1302 = &((cc0_deref(struct _c0_Node, _c0v_tmp))._c0_val);
    cc0_deref(int, _c0t__tmp_1302) = _c0v_val;
    struct _c0_Node** _c0t__tmp_1303;
    _c0t__tmp_1303 = &((cc0_deref(struct _c0_Node, _c0v_tmp))._c0_next);
    struct _c0_Node* _c0t__tmp_1304 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
    cc0_deref(struct _c0_Node*, _c0t__tmp_1303) = _c0t__tmp_1304;
    struct _c0_Node** _c0t__tmp_1305;
    _c0t__tmp_1305 = &((cc0_deref(struct _c0_Node, _c0v_curr))._c0_next);
    cc0_deref(struct _c0_Node*, _c0t__tmp_1305) = _c0v_tmp;
    if ((_c0v_head == _c0v_curr)) {
    } else {
      struct _c0_Node* _c0t__tmp_1306 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
      _c0_remove_segHelper(_c0t__tmp_1306, _c0v_curr, _c0v__ownedFields);
      if (!((_c0v__ == NULL))) {
        int _c0t__tmp_1307 = (cc0_deref(struct _c0_Node, _c0v__))._c0__id;
        _c0_loseAcc(_c0v__ownedFields, _c0t__tmp_1307, 0);
        int _c0t__tmp_1308 = (cc0_deref(struct _c0_Node, _c0v__))._c0__id;
        _c0_loseAcc(_c0v__ownedFields, _c0t__tmp_1308, 1);
      }
      if (!((_c0v_curr == _c0v__))) {
        int _c0t__tmp_1309 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
        _c0_loseAcc(_c0v__ownedFields, _c0t__tmp_1309, 0);
        int _c0t__tmp_1310 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
        _c0_loseAcc(_c0v__ownedFields, _c0t__tmp_1310, 1);
        struct _c0_Node* _c0t__tmp_1311 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        _c0_remove_segHelper(_c0t__tmp_1311, _c0v__, _c0v__ownedFields);
      }
      struct _c0_Node* _c0t__tmp_1312 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
      int* _c0t__tmp_1313 = (cc0_deref(struct _c0_OwnedFields, _c0v__ownedFields))._c0_instanceCounter;
      _c0_appendLemmaAfterLoopBody(_c0t__tmp_1312, _c0v_curr, NULL, _c0t__tmp_1313);
      struct _c0_Node* _c0t__tmp_1314 = (cc0_deref(struct _c0_Node, _c0v_head))._c0_next;
      _c0_add_segHelper(_c0t__tmp_1314, _c0v__, _c0v__ownedFields);
      if (!((_c0v__ == NULL))) {
        int _c0t__tmp_1315 = (cc0_deref(struct _c0_Node, _c0v__))._c0__id;
        _c0_addAcc(_c0v__ownedFields, _c0t__tmp_1315, 3, 0);
        int _c0t__tmp_1316 = (cc0_deref(struct _c0_Node, _c0v__))._c0__id;
        _c0_addAcc(_c0v__ownedFields, _c0t__tmp_1316, 3, 1);
      }
    }
    return _c0v_head;
  }
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_remove_segHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, struct _c0_OwnedFields* _c0v__ownedFields) {
  if (!((_c0v_start == _c0v_end))) {
    int _c0t__tmp_1317 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_loseAcc(_c0v__ownedFields, _c0t__tmp_1317, 0);
    int _c0t__tmp_1318 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_loseAcc(_c0v__ownedFields, _c0t__tmp_1318, 1);
    struct _c0_Node* _c0t__tmp_1319 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    _c0_remove_segHelper(_c0t__tmp_1319, _c0v_end, _c0v__ownedFields);
  }
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_segHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, struct _c0_OwnedFields* _c0v__ownedFields) {
  if ((_c0v_start == _c0v_end)) {
    cc0_assert(true, c0_string_fromliteral("src/test/resources/runtime-analysis/stack.verified.c0: 405.5-405.18: assert failed"));
  } else {
    int _c0t__tmp_1321;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_1320 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_1321 = _c0t__tmp_1320;
    } else {
      _c0t__tmp_1321 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1321, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
    int _c0t__tmp_1323;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_1322 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_1323 = _c0t__tmp_1322;
    } else {
      _c0t__tmp_1323 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1323, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
    struct _c0_Node* _c0t__tmp_1324 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    _c0_segHelper(_c0t__tmp_1324, _c0v_end, _c0v__ownedFields);
  }
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sep_segHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, struct _c0_OwnedFields* _c0v__ownedFields) {
  if (!((_c0v_start == _c0v_end))) {
    int _c0t__tmp_1326;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_1325 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_1326 = _c0t__tmp_1325;
    } else {
      _c0t__tmp_1326 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__ownedFields, _c0t__tmp_1326, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
    int _c0t__tmp_1328;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_1327 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_1328 = _c0t__tmp_1327;
    } else {
      _c0t__tmp_1328 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__ownedFields, _c0t__tmp_1328, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
    struct _c0_Node* _c0t__tmp_1329 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    _c0_sep_segHelper(_c0t__tmp_1329, _c0v_end, _c0v__ownedFields);
  }
}
long map_length = 2342;
const char* source_map[2342] = {
  [70] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 15.12-15.31",
  [78] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 20.3-20.26",
  [79] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 20.3-20.44",
  [82] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 22.3-22.19",
  [83] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 22.22-22.48",
  [84] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 22.3-22.48",
  [86] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 23.3-23.19",
  [87] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 23.47-23.63",
  [89] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 23.3-23.64",
  [93] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 25.22-25.38",
  [99] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 26.5-26.21",
  [101] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 26.5-26.24",
  [102] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 26.5-26.31",
  [111] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 34.21-34.37",
  [114] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 35.3-35.19",
  [115] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 35.22-35.48",
  [116] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 35.3-35.48",
  [117] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 36.56-36.72",
  [125] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 38.8-38.24",
  [126] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 38.8-38.27",
  [128] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 38.40-38.56",
  [129] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 38.40-38.59",
  [130] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 38.40-38.68",
  [136] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 39.19-39.35",
  [137] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 39.19-39.38",
  [138] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 39.19-39.43",
  [140] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 40.34-40.50",
  [141] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 40.24-40.51",
  [144] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 41.15-41.36",
  [149] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 42.41-42.57",
  [150] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 42.24-42.57",
  [154] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 44.9-44.30",
  [155] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 44.33-44.49",
  [156] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 44.33-44.52",
  [157] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 44.9-44.52",
  [164] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 47.3-47.19",
  [165] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 47.3-47.33",
  [170] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 52.27-52.43",
  [171] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 52.17-52.44",
  [174] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 53.11-53.27",
  [175] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 53.11-53.34",
  [181] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 54.13-54.29",
  [182] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 54.13-54.36",
  [183] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 54.13-54.45",
  [185] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 54.49-54.65",
  [186] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 54.49-54.72",
  [187] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 54.49-54.77",
  [193] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 55.20-55.36",
  [194] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 55.20-55.43",
  [197] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 57.35-57.51",
  [198] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 57.21-57.51",
  [207] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 68.6-68.20",
  [208] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 68.24-68.40",
  [210] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 68.51-68.63",
  [212] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 70.30-70.46",
  [213] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 70.20-70.47",
  [217] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.9-71.25",
  [218] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.9-71.37",
  [220] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.50-71.66",
  [221] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.50-71.78",
  [222] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.50-71.87",
  [231] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.121-71.137",
  [232] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 71.102-71.137",
  [237] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 74.3-74.19",
  [239] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 74.3-74.31",
  [240] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 74.3-74.39",
  [241] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 75.3-75.22",
  [243] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 77.3-77.18",
  [245] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 77.3-77.49",
  [247] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 78.3-78.16",
  [248] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 78.3-78.28",
  [250] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 79.3-79.13",
  [251] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 79.3-79.19",
  [253] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 80.3-80.17",
  [254] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 80.3-80.25",
  [258] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 82.20-82.33",
  [264] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 83.5-83.20",
  [266] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 83.5-83.23",
  [267] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 83.5-83.32",
  [274] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 86.5-86.25",
  [275] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 86.28-86.41",
  [276] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 86.5-86.41",
  [279] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 88.5-88.25",
  [280] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 88.5-88.29",
  [282] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 90.10-90.26",
  [283] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 90.10-90.38",
  [288] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 94.28-94.51",
  [289] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 94.27-94.51",
  [290] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 94.5-94.69",
  [291] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 95.7-95.30",
  [292] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 95.5-95.36",
  [293] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 96.14-96.37",
  [294] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 96.12-96.38",
  [299] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 100.24-100.41",
  [302] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 102.9-102.24",
  [303] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 102.9-102.36",
  [305] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 103.9-103.34",
  [306] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 104.9-104.24",
  [308] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 104.9-104.36",
  [309] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 104.9-104.43",
  [312] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 107.13-107.57",
  [314] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 108.5-108.20",
  [316] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 108.5-108.32",
  [317] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 108.5-108.39",
  [318] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 109.5-109.30",
  [323] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 114.27-114.44",
  [329] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 115.28-115.45",
  [330] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 115.28-115.57",
  [334] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 116.9-116.29",
  [340] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 121.27-121.44",
  [343] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 123.19-123.63",
  [346] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 124.16-124.33",
  [347] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 124.16-124.45",
  [349] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 125.9-125.29",
  [353] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 127.5-127.22",
  [355] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 127.5-127.34",
  [356] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 127.5-127.41",
  [357] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 128.5-128.32",
  [361] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 132.27-132.44",
  [364] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 134.26-134.40",
  [366] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 135.13-135.85",
  [369] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 136.18-136.34",
  [370] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 136.18-136.46",
  [372] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 137.13-137.29",
  [374] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 137.13-137.41",
  [375] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 137.13-137.49",
  [376] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 138.13-138.39",
  [379] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 140.12-140.33",
  [382] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 140.40-140.55",
  [383] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 140.40-140.62",
  [392] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 146.26-146.42",
  [398] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 147.38-147.54",
  [399] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 147.38-147.57",
  [404] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 149.35-149.53",
  [410] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 150.36-150.51",
  [411] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 150.53-150.71",
  [412] = "/home/jpvinnie/Documents/uni/cmu/gvc0/src/main/resources/runtime.c0: 150.21-150.75",
  [479] = "src/test/resources/runtime-analysis/stack.verified.c0: 28.3-28.63",
  [488] = "src/test/resources/runtime-analysis/stack.verified.c0: 35.26-35.36",
  [489] = "src/test/resources/runtime-analysis/stack.verified.c0: 35.5-35.43",
  [490] = "src/test/resources/runtime-analysis/stack.verified.c0: 36.26-36.36",
  [491] = "src/test/resources/runtime-analysis/stack.verified.c0: 36.5-36.40",
  [492] = "src/test/resources/runtime-analysis/stack.verified.c0: 37.26-37.36",
  [493] = "src/test/resources/runtime-analysis/stack.verified.c0: 37.5-37.43",
  [494] = "src/test/resources/runtime-analysis/stack.verified.c0: 38.26-38.36",
  [495] = "src/test/resources/runtime-analysis/stack.verified.c0: 38.5-38.40",
  [496] = "src/test/resources/runtime-analysis/stack.verified.c0: 39.26-39.37",
  [497] = "src/test/resources/runtime-analysis/stack.verified.c0: 39.5-39.70",
  [504] = "src/test/resources/runtime-analysis/stack.verified.c0: 45.3-45.43",
  [512] = "src/test/resources/runtime-analysis/stack.verified.c0: 52.26-52.36",
  [513] = "src/test/resources/runtime-analysis/stack.verified.c0: 52.5-52.43",
  [514] = "src/test/resources/runtime-analysis/stack.verified.c0: 53.26-53.36",
  [515] = "src/test/resources/runtime-analysis/stack.verified.c0: 53.5-53.43",
  [516] = "src/test/resources/runtime-analysis/stack.verified.c0: 54.19-54.30",
  [517] = "src/test/resources/runtime-analysis/stack.verified.c0: 54.5-54.50",
  [529] = "src/test/resources/runtime-analysis/stack.verified.c0: 70.32-70.39",
  [530] = "src/test/resources/runtime-analysis/stack.verified.c0: 70.7-70.64",
  [553] = "src/test/resources/runtime-analysis/stack.verified.c0: 93.45-93.51",
  [558] = "src/test/resources/runtime-analysis/stack.verified.c0: 93.9-93.118",
  [563] = "src/test/resources/runtime-analysis/stack.verified.c0: 97.45-97.51",
  [568] = "src/test/resources/runtime-analysis/stack.verified.c0: 97.9-97.117",
  [571] = "src/test/resources/runtime-analysis/stack.verified.c0: 101.9-101.30",
  [574] = "src/test/resources/runtime-analysis/stack.verified.c0: 105.19-105.26",
  [575] = "src/test/resources/runtime-analysis/stack.verified.c0: 105.9-105.44",
  [579] = "src/test/resources/runtime-analysis/stack.verified.c0: 111.27-111.34",
  [580] = "src/test/resources/runtime-analysis/stack.verified.c0: 111.7-111.55",
  [584] = "src/test/resources/runtime-analysis/stack.verified.c0: 114.45-114.51",
  [589] = "src/test/resources/runtime-analysis/stack.verified.c0: 114.9-114.117",
  [594] = "src/test/resources/runtime-analysis/stack.verified.c0: 118.45-118.51",
  [599] = "src/test/resources/runtime-analysis/stack.verified.c0: 118.9-118.118",
  [602] = "src/test/resources/runtime-analysis/stack.verified.c0: 122.19-122.26",
  [603] = "src/test/resources/runtime-analysis/stack.verified.c0: 122.9-122.44",
  [614] = "src/test/resources/runtime-analysis/stack.verified.c0: 132.3-132.9",
  [615] = "src/test/resources/runtime-analysis/stack.verified.c0: 132.12-132.29",
  [616] = "src/test/resources/runtime-analysis/stack.verified.c0: 132.3-132.29",
  [617] = "src/test/resources/runtime-analysis/stack.verified.c0: 133.23-133.40",
  [618] = "src/test/resources/runtime-analysis/stack.verified.c0: 133.3-133.44",
  [620] = "src/test/resources/runtime-analysis/stack.verified.c0: 134.3-134.9",
  [621] = "src/test/resources/runtime-analysis/stack.verified.c0: 134.3-134.15",
  [623] = "src/test/resources/runtime-analysis/stack.verified.c0: 135.3-135.10",
  [624] = "src/test/resources/runtime-analysis/stack.verified.c0: 135.3-135.17",
  [636] = "src/test/resources/runtime-analysis/stack.verified.c0: 147.18-147.51",
  [638] = "src/test/resources/runtime-analysis/stack.verified.c0: 148.7-148.39",
  [640] = "src/test/resources/runtime-analysis/stack.verified.c0: 149.3-149.27",
  [641] = "src/test/resources/runtime-analysis/stack.verified.c0: 150.17-150.50",
  [643] = "src/test/resources/runtime-analysis/stack.verified.c0: 151.3-151.47",
  [644] = "src/test/resources/runtime-analysis/stack.verified.c0: 152.8-152.31",
  [646] = "src/test/resources/runtime-analysis/stack.verified.c0: 153.3-153.28",
  [647] = "src/test/resources/runtime-analysis/stack.verified.c0: 154.3-154.24",
  [668] = "src/test/resources/runtime-analysis/stack.verified.c0: 177.36-177.65",
  [669] = "src/test/resources/runtime-analysis/stack.verified.c0: 177.20-177.66",
  [674] = "src/test/resources/runtime-analysis/stack.verified.c0: 178.23-178.33",
  [684] = "src/test/resources/runtime-analysis/stack.verified.c0: 178.60-178.70",
  [694] = "src/test/resources/runtime-analysis/stack.verified.c0: 180.46-180.55",
  [699] = "src/test/resources/runtime-analysis/stack.verified.c0: 180.7-180.122",
  [704] = "src/test/resources/runtime-analysis/stack.verified.c0: 184.46-184.55",
  [709] = "src/test/resources/runtime-analysis/stack.verified.c0: 184.7-184.121",
  [713] = "src/test/resources/runtime-analysis/stack.verified.c0: 186.23-186.33",
  [720] = "src/test/resources/runtime-analysis/stack.verified.c0: 188.31-188.41",
  [722] = "src/test/resources/runtime-analysis/stack.verified.c0: 188.52-188.62",
  [723] = "src/test/resources/runtime-analysis/stack.verified.c0: 188.52-188.67",
  [728] = "src/test/resources/runtime-analysis/stack.verified.c0: 188.7-188.133",
  [730] = "src/test/resources/runtime-analysis/stack.verified.c0: 189.31-189.41",
  [732] = "src/test/resources/runtime-analysis/stack.verified.c0: 189.52-189.62",
  [733] = "src/test/resources/runtime-analysis/stack.verified.c0: 189.52-189.67",
  [738] = "src/test/resources/runtime-analysis/stack.verified.c0: 189.7-189.134",
  [743] = "src/test/resources/runtime-analysis/stack.verified.c0: 191.23-191.33",
  [753] = "src/test/resources/runtime-analysis/stack.verified.c0: 191.60-191.70",
  [761] = "src/test/resources/runtime-analysis/stack.verified.c0: 193.16-193.26",
  [762] = "src/test/resources/runtime-analysis/stack.verified.c0: 193.7-193.37",
  [766] = "src/test/resources/runtime-analysis/stack.verified.c0: 195.55-195.64",
  [771] = "src/test/resources/runtime-analysis/stack.verified.c0: 195.5-195.129",
  [774] = "src/test/resources/runtime-analysis/stack.verified.c0: 196.55-196.64",
  [779] = "src/test/resources/runtime-analysis/stack.verified.c0: 196.5-196.130",
  [780] = "src/test/resources/runtime-analysis/stack.verified.c0: 197.11-197.21",
  [783] = "src/test/resources/runtime-analysis/stack.verified.c0: 199.42-199.52",
  [785] = "src/test/resources/runtime-analysis/stack.verified.c0: 199.63-199.73",
  [786] = "src/test/resources/runtime-analysis/stack.verified.c0: 199.63-199.78",
  [791] = "src/test/resources/runtime-analysis/stack.verified.c0: 199.7-199.144",
  [793] = "src/test/resources/runtime-analysis/stack.verified.c0: 200.42-200.52",
  [795] = "src/test/resources/runtime-analysis/stack.verified.c0: 200.63-200.73",
  [796] = "src/test/resources/runtime-analysis/stack.verified.c0: 200.63-200.78",
  [801] = "src/test/resources/runtime-analysis/stack.verified.c0: 200.7-200.143",
  [805] = "src/test/resources/runtime-analysis/stack.verified.c0: 202.34-202.44",
  [815] = "src/test/resources/runtime-analysis/stack.verified.c0: 203.36-203.46",
  [821] = "src/test/resources/runtime-analysis/stack.verified.c0: 203.80-203.90",
  [822] = "src/test/resources/runtime-analysis/stack.verified.c0: 203.80-203.96",
  [828] = "src/test/resources/runtime-analysis/stack.verified.c0: 203.111-203.121",
  [836] = "src/test/resources/runtime-analysis/stack.verified.c0: 204.34-204.44",
  [844] = "src/test/resources/runtime-analysis/stack.verified.c0: 205.12-205.22",
  [846] = "src/test/resources/runtime-analysis/stack.verified.c0: 205.34-205.44",
  [847] = "src/test/resources/runtime-analysis/stack.verified.c0: 205.34-205.50",
  [857] = "src/test/resources/runtime-analysis/stack.verified.c0: 208.14-208.24",
  [865] = "src/test/resources/runtime-analysis/stack.verified.c0: 217.50-217.59",
  [870] = "src/test/resources/runtime-analysis/stack.verified.c0: 217.11-217.126",
  [872] = "src/test/resources/runtime-analysis/stack.verified.c0: 219.29-219.39",
  [873] = "src/test/resources/runtime-analysis/stack.verified.c0: 219.9-219.66",
  [875] = "src/test/resources/runtime-analysis/stack.verified.c0: 221.37-221.66",
  [876] = "src/test/resources/runtime-analysis/stack.verified.c0: 221.21-221.67",
  [895] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.60-222.70",
  [905] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.132-222.142",
  [917] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.204-222.214",
  [929] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.274-222.284",
  [941] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.439-222.449",
  [953] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.511-222.521",
  [965] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.583-222.593",
  [977] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.653-222.663",
  [989] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.817-222.827",
  [1001] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.888-222.898",
  [1013] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.959-222.969",
  [1025] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.1028-222.1038",
  [1037] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.1190-222.1200",
  [1049] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.1261-222.1271",
  [1061] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.1332-222.1342",
  [1073] = "src/test/resources/runtime-analysis/stack.verified.c0: 222.1401-222.1411",
  [1083] = "src/test/resources/runtime-analysis/stack.verified.c0: 224.48-224.57",
  [1088] = "src/test/resources/runtime-analysis/stack.verified.c0: 224.9-224.124",
  [1093] = "src/test/resources/runtime-analysis/stack.verified.c0: 228.48-228.57",
  [1098] = "src/test/resources/runtime-analysis/stack.verified.c0: 228.9-228.123",
  [1133] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.59-230.69",
  [1143] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.142-230.152",
  [1155] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.225-230.235",
  [1167] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.297-230.307",
  [1179] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.381-230.391",
  [1191] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.465-230.475",
  [1203] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.535-230.545",
  [1215] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.616-230.626",
  [1227] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.698-230.708",
  [1239] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.781-230.791",
  [1251] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.864-230.874",
  [1263] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.936-230.946",
  [1275] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1020-230.1030",
  [1287] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1104-230.1114",
  [1299] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1174-230.1184",
  [1311] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1255-230.1265",
  [1323] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1336-230.1346",
  [1335] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1418-230.1428",
  [1347] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1500-230.1510",
  [1359] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1571-230.1581",
  [1371] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1654-230.1664",
  [1383] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1737-230.1747",
  [1395] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1806-230.1816",
  [1407] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1886-230.1896",
  [1419] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.1967-230.1977",
  [1431] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.2049-230.2059",
  [1443] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.2131-230.2141",
  [1455] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.2202-230.2212",
  [1467] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.2285-230.2295",
  [1479] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.2368-230.2378",
  [1491] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.2437-230.2447",
  [1503] = "src/test/resources/runtime-analysis/stack.verified.c0: 230.2517-230.2527",
  [1512] = "src/test/resources/runtime-analysis/stack.verified.c0: 232.33-232.43",
  [1514] = "src/test/resources/runtime-analysis/stack.verified.c0: 232.54-232.64",
  [1515] = "src/test/resources/runtime-analysis/stack.verified.c0: 232.54-232.69",
  [1520] = "src/test/resources/runtime-analysis/stack.verified.c0: 232.9-232.136",
  [1531] = "src/test/resources/runtime-analysis/stack.verified.c0: 234.59-234.69",
  [1541] = "src/test/resources/runtime-analysis/stack.verified.c0: 234.131-234.141",
  [1553] = "src/test/resources/runtime-analysis/stack.verified.c0: 234.202-234.212",
  [1565] = "src/test/resources/runtime-analysis/stack.verified.c0: 234.274-234.284",
  [1577] = "src/test/resources/runtime-analysis/stack.verified.c0: 234.344-234.354",
  [1589] = "src/test/resources/runtime-analysis/stack.verified.c0: 234.415-234.425",
  [1601] = "src/test/resources/runtime-analysis/stack.verified.c0: 234.485-234.495",
  [1613] = "src/test/resources/runtime-analysis/stack.verified.c0: 234.556-234.566",
  [1622] = "src/test/resources/runtime-analysis/stack.verified.c0: 236.33-236.43",
  [1624] = "src/test/resources/runtime-analysis/stack.verified.c0: 236.54-236.64",
  [1625] = "src/test/resources/runtime-analysis/stack.verified.c0: 236.54-236.69",
  [1630] = "src/test/resources/runtime-analysis/stack.verified.c0: 236.9-236.135",
  [1637] = "src/test/resources/runtime-analysis/stack.verified.c0: 238.59-238.69",
  [1647] = "src/test/resources/runtime-analysis/stack.verified.c0: 238.130-238.140",
  [1659] = "src/test/resources/runtime-analysis/stack.verified.c0: 238.200-238.210",
  [1671] = "src/test/resources/runtime-analysis/stack.verified.c0: 238.270-238.280",
  [1680] = "src/test/resources/runtime-analysis/stack.verified.c0: 240.19-240.29",
  [1681] = "src/test/resources/runtime-analysis/stack.verified.c0: 240.19-240.35",
  [1682] = "src/test/resources/runtime-analysis/stack.verified.c0: 240.19-240.41",
  [1684] = "src/test/resources/runtime-analysis/stack.verified.c0: 240.56-240.66",
  [1690] = "src/test/resources/runtime-analysis/stack.verified.c0: 240.83-240.93",
  [1691] = "src/test/resources/runtime-analysis/stack.verified.c0: 240.83-240.99",
  [1692] = "src/test/resources/runtime-analysis/stack.verified.c0: 240.83-240.105",
  [1694] = "src/test/resources/runtime-analysis/stack.verified.c0: 240.120-240.130",
  [1699] = "src/test/resources/runtime-analysis/stack.verified.c0: 240.9-240.142",
  [1710] = "src/test/resources/runtime-analysis/stack.verified.c0: 242.60-242.70",
  [1720] = "src/test/resources/runtime-analysis/stack.verified.c0: 242.132-242.142",
  [1732] = "src/test/resources/runtime-analysis/stack.verified.c0: 242.204-242.214",
  [1744] = "src/test/resources/runtime-analysis/stack.verified.c0: 242.276-242.286",
  [1756] = "src/test/resources/runtime-analysis/stack.verified.c0: 242.347-242.357",
  [1768] = "src/test/resources/runtime-analysis/stack.verified.c0: 242.418-242.428",
  [1780] = "src/test/resources/runtime-analysis/stack.verified.c0: 242.489-242.499",
  [1792] = "src/test/resources/runtime-analysis/stack.verified.c0: 242.560-242.570",
  [1800] = "src/test/resources/runtime-analysis/stack.verified.c0: 244.18-244.28",
  [1801] = "src/test/resources/runtime-analysis/stack.verified.c0: 244.9-244.39",
  [1812] = "src/test/resources/runtime-analysis/stack.verified.c0: 246.60-246.70",
  [1822] = "src/test/resources/runtime-analysis/stack.verified.c0: 246.130-246.140",
  [1834] = "src/test/resources/runtime-analysis/stack.verified.c0: 246.201-246.211",
  [1846] = "src/test/resources/runtime-analysis/stack.verified.c0: 246.271-246.281",
  [1858] = "src/test/resources/runtime-analysis/stack.verified.c0: 246.341-246.351",
  [1870] = "src/test/resources/runtime-analysis/stack.verified.c0: 246.410-246.420",
  [1882] = "src/test/resources/runtime-analysis/stack.verified.c0: 246.480-246.490",
  [1894] = "src/test/resources/runtime-analysis/stack.verified.c0: 246.549-246.559",
  [1903] = "src/test/resources/runtime-analysis/stack.verified.c0: 248.19-248.29",
  [1904] = "src/test/resources/runtime-analysis/stack.verified.c0: 248.19-248.35",
  [1906] = "src/test/resources/runtime-analysis/stack.verified.c0: 248.50-248.60",
  [1912] = "src/test/resources/runtime-analysis/stack.verified.c0: 248.77-248.87",
  [1913] = "src/test/resources/runtime-analysis/stack.verified.c0: 248.77-248.93",
  [1915] = "src/test/resources/runtime-analysis/stack.verified.c0: 248.108-248.118",
  [1920] = "src/test/resources/runtime-analysis/stack.verified.c0: 248.9-248.130",
  [1924] = "src/test/resources/runtime-analysis/stack.verified.c0: 250.56-250.65",
  [1929] = "src/test/resources/runtime-analysis/stack.verified.c0: 250.7-250.130",
  [1932] = "src/test/resources/runtime-analysis/stack.verified.c0: 251.56-251.65",
  [1937] = "src/test/resources/runtime-analysis/stack.verified.c0: 251.7-251.131",
  [1938] = "src/test/resources/runtime-analysis/stack.verified.c0: 252.13-252.23",
  [1941] = "src/test/resources/runtime-analysis/stack.verified.c0: 254.43-254.53",
  [1943] = "src/test/resources/runtime-analysis/stack.verified.c0: 254.64-254.74",
  [1944] = "src/test/resources/runtime-analysis/stack.verified.c0: 254.64-254.79",
  [1949] = "src/test/resources/runtime-analysis/stack.verified.c0: 254.9-254.145",
  [1951] = "src/test/resources/runtime-analysis/stack.verified.c0: 255.43-255.53",
  [1953] = "src/test/resources/runtime-analysis/stack.verified.c0: 255.64-255.74",
  [1954] = "src/test/resources/runtime-analysis/stack.verified.c0: 255.64-255.79",
  [1959] = "src/test/resources/runtime-analysis/stack.verified.c0: 255.9-255.144",
  [1963] = "src/test/resources/runtime-analysis/stack.verified.c0: 258.5-258.15",
  [1964] = "src/test/resources/runtime-analysis/stack.verified.c0: 258.5-258.22",
  [1989] = "src/test/resources/runtime-analysis/stack.verified.c0: 282.3-282.30",
  [1996] = "src/test/resources/runtime-analysis/stack.verified.c0: 288.5-288.11",
  [1997] = "src/test/resources/runtime-analysis/stack.verified.c0: 288.14-288.43",
  [1998] = "src/test/resources/runtime-analysis/stack.verified.c0: 288.5-288.43",
  [2000] = "src/test/resources/runtime-analysis/stack.verified.c0: 289.5-289.11",
  [2001] = "src/test/resources/runtime-analysis/stack.verified.c0: 289.5-289.17",
  [2003] = "src/test/resources/runtime-analysis/stack.verified.c0: 290.5-290.12",
  [2004] = "src/test/resources/runtime-analysis/stack.verified.c0: 290.5-290.19",
  [2010] = "src/test/resources/runtime-analysis/stack.verified.c0: 296.34-296.44",
  [2019] = "src/test/resources/runtime-analysis/stack.verified.c0: 298.34-298.44",
  [2027] = "src/test/resources/runtime-analysis/stack.verified.c0: 299.34-299.44",
  [2034] = "src/test/resources/runtime-analysis/stack.verified.c0: 300.12-300.22",
  [2040] = "src/test/resources/runtime-analysis/stack.verified.c0: 303.14-303.24",
  [2047] = "src/test/resources/runtime-analysis/stack.verified.c0: 312.29-312.39",
  [2048] = "src/test/resources/runtime-analysis/stack.verified.c0: 312.9-312.66",
  [2053] = "src/test/resources/runtime-analysis/stack.verified.c0: 316.48-316.57",
  [2058] = "src/test/resources/runtime-analysis/stack.verified.c0: 316.9-316.123",
  [2063] = "src/test/resources/runtime-analysis/stack.verified.c0: 320.48-320.57",
  [2068] = "src/test/resources/runtime-analysis/stack.verified.c0: 320.9-320.124",
  [2071] = "src/test/resources/runtime-analysis/stack.verified.c0: 324.19-324.29",
  [2072] = "src/test/resources/runtime-analysis/stack.verified.c0: 324.9-324.50",
  [2078] = "src/test/resources/runtime-analysis/stack.verified.c0: 329.48-329.57",
  [2083] = "src/test/resources/runtime-analysis/stack.verified.c0: 329.9-329.124",
  [2087] = "src/test/resources/runtime-analysis/stack.verified.c0: 331.37-331.47",
  [2093] = "src/test/resources/runtime-analysis/stack.verified.c0: 332.37-332.66",
  [2094] = "src/test/resources/runtime-analysis/stack.verified.c0: 332.21-332.67",
  [2099] = "src/test/resources/runtime-analysis/stack.verified.c0: 335.48-335.57",
  [2104] = "src/test/resources/runtime-analysis/stack.verified.c0: 335.9-335.123",
  [2111] = "src/test/resources/runtime-analysis/stack.verified.c0: 337.145-337.155",
  [2121] = "src/test/resources/runtime-analysis/stack.verified.c0: 337.302-337.312",
  [2133] = "src/test/resources/runtime-analysis/stack.verified.c0: 337.457-337.467",
  [2145] = "src/test/resources/runtime-analysis/stack.verified.c0: 337.612-337.622",
  [2154] = "src/test/resources/runtime-analysis/stack.verified.c0: 339.33-339.43",
  [2156] = "src/test/resources/runtime-analysis/stack.verified.c0: 339.54-339.64",
  [2157] = "src/test/resources/runtime-analysis/stack.verified.c0: 339.54-339.69",
  [2162] = "src/test/resources/runtime-analysis/stack.verified.c0: 339.9-339.135",
  [2164] = "src/test/resources/runtime-analysis/stack.verified.c0: 340.33-340.43",
  [2166] = "src/test/resources/runtime-analysis/stack.verified.c0: 340.54-340.64",
  [2167] = "src/test/resources/runtime-analysis/stack.verified.c0: 340.54-340.69",
  [2172] = "src/test/resources/runtime-analysis/stack.verified.c0: 340.9-340.136",
  [2173] = "src/test/resources/runtime-analysis/stack.verified.c0: 341.19-341.29",
  [2174] = "src/test/resources/runtime-analysis/stack.verified.c0: 341.19-341.35",
  [2175] = "src/test/resources/runtime-analysis/stack.verified.c0: 341.9-341.56",
  [2178] = "src/test/resources/runtime-analysis/stack.verified.c0: 345.9-345.44",
  [2182] = "src/test/resources/runtime-analysis/stack.verified.c0: 347.56-347.65",
  [2187] = "src/test/resources/runtime-analysis/stack.verified.c0: 347.7-347.130",
  [2190] = "src/test/resources/runtime-analysis/stack.verified.c0: 348.56-348.65",
  [2195] = "src/test/resources/runtime-analysis/stack.verified.c0: 348.7-348.131",
  [2196] = "src/test/resources/runtime-analysis/stack.verified.c0: 349.7-349.45",
  [2197] = "src/test/resources/runtime-analysis/stack.verified.c0: 350.13-350.23",
  [2200] = "src/test/resources/runtime-analysis/stack.verified.c0: 352.43-352.53",
  [2202] = "src/test/resources/runtime-analysis/stack.verified.c0: 352.64-352.74",
  [2203] = "src/test/resources/runtime-analysis/stack.verified.c0: 352.64-352.79",
  [2208] = "src/test/resources/runtime-analysis/stack.verified.c0: 352.9-352.145",
  [2210] = "src/test/resources/runtime-analysis/stack.verified.c0: 353.43-353.53",
  [2212] = "src/test/resources/runtime-analysis/stack.verified.c0: 353.64-353.74",
  [2213] = "src/test/resources/runtime-analysis/stack.verified.c0: 353.64-353.79",
  [2218] = "src/test/resources/runtime-analysis/stack.verified.c0: 353.9-353.144",
  [2219] = "src/test/resources/runtime-analysis/stack.verified.c0: 354.23-354.33",
  [2220] = "src/test/resources/runtime-analysis/stack.verified.c0: 354.23-354.39",
  [2221] = "src/test/resources/runtime-analysis/stack.verified.c0: 354.9-354.59",
  [2227] = "src/test/resources/runtime-analysis/stack.verified.c0: 358.5-358.13",
  [2228] = "src/test/resources/runtime-analysis/stack.verified.c0: 358.16-358.45",
  [2229] = "src/test/resources/runtime-analysis/stack.verified.c0: 358.5-358.45",
  [2231] = "src/test/resources/runtime-analysis/stack.verified.c0: 359.5-359.13",
  [2232] = "src/test/resources/runtime-analysis/stack.verified.c0: 359.5-359.19",
  [2234] = "src/test/resources/runtime-analysis/stack.verified.c0: 360.5-360.14",
  [2235] = "src/test/resources/runtime-analysis/stack.verified.c0: 360.17-360.27",
  [2236] = "src/test/resources/runtime-analysis/stack.verified.c0: 360.5-360.27",
  [2238] = "src/test/resources/runtime-analysis/stack.verified.c0: 361.5-361.15",
  [2239] = "src/test/resources/runtime-analysis/stack.verified.c0: 361.5-361.21",
  [2242] = "src/test/resources/runtime-analysis/stack.verified.c0: 367.24-367.34",
  [2243] = "src/test/resources/runtime-analysis/stack.verified.c0: 367.7-367.55",
  [2245] = "src/test/resources/runtime-analysis/stack.verified.c0: 370.31-370.37",
  [2246] = "src/test/resources/runtime-analysis/stack.verified.c0: 370.9-370.41",
  [2247] = "src/test/resources/runtime-analysis/stack.verified.c0: 371.31-371.37",
  [2248] = "src/test/resources/runtime-analysis/stack.verified.c0: 371.9-371.41",
  [2251] = "src/test/resources/runtime-analysis/stack.verified.c0: 375.31-375.40",
  [2252] = "src/test/resources/runtime-analysis/stack.verified.c0: 375.9-375.44",
  [2253] = "src/test/resources/runtime-analysis/stack.verified.c0: 376.31-376.40",
  [2254] = "src/test/resources/runtime-analysis/stack.verified.c0: 376.9-376.44",
  [2255] = "src/test/resources/runtime-analysis/stack.verified.c0: 377.26-377.36",
  [2256] = "src/test/resources/runtime-analysis/stack.verified.c0: 377.9-377.54",
  [2258] = "src/test/resources/runtime-analysis/stack.verified.c0: 379.32-379.42",
  [2259] = "src/test/resources/runtime-analysis/stack.verified.c0: 379.56-379.85",
  [2260] = "src/test/resources/runtime-analysis/stack.verified.c0: 379.7-379.86",
  [2261] = "src/test/resources/runtime-analysis/stack.verified.c0: 380.21-380.31",
  [2262] = "src/test/resources/runtime-analysis/stack.verified.c0: 380.7-380.49",
  [2264] = "src/test/resources/runtime-analysis/stack.verified.c0: 383.30-383.36",
  [2265] = "src/test/resources/runtime-analysis/stack.verified.c0: 383.9-383.43",
  [2266] = "src/test/resources/runtime-analysis/stack.verified.c0: 384.30-384.36",
  [2267] = "src/test/resources/runtime-analysis/stack.verified.c0: 384.9-384.43",
  [2279] = "src/test/resources/runtime-analysis/stack.verified.c0: 395.27-395.37",
  [2280] = "src/test/resources/runtime-analysis/stack.verified.c0: 395.5-395.41",
  [2281] = "src/test/resources/runtime-analysis/stack.verified.c0: 396.27-396.37",
  [2282] = "src/test/resources/runtime-analysis/stack.verified.c0: 396.5-396.41",
  [2283] = "src/test/resources/runtime-analysis/stack.verified.c0: 397.22-397.33",
  [2284] = "src/test/resources/runtime-analysis/stack.verified.c0: 397.5-397.53",
  [2293] = "src/test/resources/runtime-analysis/stack.verified.c0: 405.5-405.18",
  [2297] = "src/test/resources/runtime-analysis/stack.verified.c0: 409.45-409.55",
  [2302] = "src/test/resources/runtime-analysis/stack.verified.c0: 409.5-409.121",
  [2305] = "src/test/resources/runtime-analysis/stack.verified.c0: 410.45-410.55",
  [2310] = "src/test/resources/runtime-analysis/stack.verified.c0: 410.5-410.122",
  [2311] = "src/test/resources/runtime-analysis/stack.verified.c0: 411.15-411.26",
  [2312] = "src/test/resources/runtime-analysis/stack.verified.c0: 411.5-411.46",
  [2323] = "src/test/resources/runtime-analysis/stack.verified.c0: 419.56-419.66",
  [2328] = "src/test/resources/runtime-analysis/stack.verified.c0: 419.5-419.131",
  [2331] = "src/test/resources/runtime-analysis/stack.verified.c0: 420.56-420.66",
  [2336] = "src/test/resources/runtime-analysis/stack.verified.c0: 420.5-420.132",
  [2337] = "src/test/resources/runtime-analysis/stack.verified.c0: 421.19-421.30",
  [2338] = "src/test/resources/runtime-analysis/stack.verified.c0: 421.5-421.50"
};
