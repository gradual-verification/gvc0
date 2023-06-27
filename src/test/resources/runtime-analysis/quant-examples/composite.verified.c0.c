#include "cc0lib.h"
#include "c0rt.h"
#include "composite.verified.c0.h"

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
  int _c0_total;
  struct _c0_Node* _c0_left;
  struct _c0_Node* _c0_right;
  struct _c0_Node* _c0_parent;
  int _c0__id;
};
struct _c0_Node* _c0_create_tree(int* _c0v__instanceCounter);
struct _c0_Node;
struct _c0_Node;
int _c0_fixup_ancestors(struct _c0_Node* _c0v_node, struct _c0_Node* _c0v_parent, int _c0v_oldTotal, int _c0v_newTotal, int* _c0v__instanceCounter);
int _c0_main();
struct _c0_Node;
struct _c0_Node* _c0_tree_add_left(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter);
struct _c0_Node;
struct _c0_Node* _c0_tree_add_right(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter);
struct _c0_Node;
struct _c0_Node* _c0_tree_get_left(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter);
struct _c0_Node;
struct _c0_Node* _c0_tree_get_parent(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter);
struct _c0_Node;
struct _c0_Node* _c0_tree_get_right(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter);
struct _c0_Node;
int _c0_tree_get_total(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter);
struct _c0_Node;
bool _c0_tree_has_left(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter);
struct _c0_Node;
bool _c0_tree_has_parent(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter);
struct _c0_Node;
bool _c0_tree_has_right(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter);

struct _c0_Node* _c0_create_tree(int* _c0v__instanceCounter) {
  struct _c0_Node* _c0v_n = NULL;
  struct _c0_Node* _c0t__tmp_135 = cc0_alloc(struct _c0_Node);
  _c0v_n = _c0t__tmp_135;
  int* _c0t__tmp_136;
  _c0t__tmp_136 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0__id);
  int _c0t__tmp_137 = cc0_deref(int, _c0v__instanceCounter);
  cc0_deref(int, _c0t__tmp_136) = _c0t__tmp_137;
  int _c0t__tmp_138 = cc0_deref(int, _c0v__instanceCounter);
  cc0_deref(int, _c0v__instanceCounter) = (_c0t__tmp_138 + 1);
  struct _c0_Node** _c0t__tmp_139;
  _c0t__tmp_139 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_left);
  cc0_deref(struct _c0_Node*, _c0t__tmp_139) = NULL;
  struct _c0_Node** _c0t__tmp_140;
  _c0t__tmp_140 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_right);
  cc0_deref(struct _c0_Node*, _c0t__tmp_140) = NULL;
  struct _c0_Node** _c0t__tmp_141;
  _c0t__tmp_141 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_parent);
  cc0_deref(struct _c0_Node*, _c0t__tmp_141) = NULL;
  int* _c0t__tmp_142;
  _c0t__tmp_142 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_total);
  cc0_deref(int, _c0t__tmp_142) = 1;
  return _c0v_n;
}

struct _c0_Node;
struct _c0_Node;
int _c0_fixup_ancestors(struct _c0_Node* _c0v_node, struct _c0_Node* _c0v_parent, int _c0v_oldTotal, int _c0v_newTotal, int* _c0v__instanceCounter) {
  struct _c0_Node* _c0v_left = NULL;
  struct _c0_Node* _c0v_right = NULL;
  struct _c0_Node* _c0v_grandparent = NULL;
  int _c0v_oldparentTotal = 0;
  int _c0v_leftTotal = 0;
  int _c0v_rightTotal = 0;
  int _c0v_parentTotal = 0;
  if ((_c0v_parent == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_143 = (cc0_deref(struct _c0_Node, _c0v_parent))._c0_left;
    _c0v_left = _c0t__tmp_143;
    struct _c0_Node* _c0t__tmp_144 = (cc0_deref(struct _c0_Node, _c0v_parent))._c0_right;
    _c0v_right = _c0t__tmp_144;
    struct _c0_Node* _c0t__tmp_145 = (cc0_deref(struct _c0_Node, _c0v_parent))._c0_parent;
    _c0v_grandparent = _c0t__tmp_145;
    int _c0t__tmp_146 = (cc0_deref(struct _c0_Node, _c0v_parent))._c0_total;
    _c0v_oldparentTotal = _c0t__tmp_146;
    _c0v_leftTotal = 0;
    _c0v_rightTotal = 0;
    if ((_c0v_node == _c0v_left)) {
      _c0v_leftTotal = _c0v_newTotal;
      if ((_c0v_right != NULL)) {
        int _c0t__tmp_147 = (cc0_deref(struct _c0_Node, _c0v_right))._c0_total;
        _c0v_rightTotal = _c0t__tmp_147;
      }
    } else {
      if ((_c0v_left != NULL)) {
        int _c0t__tmp_148 = (cc0_deref(struct _c0_Node, _c0v_left))._c0_total;
        _c0v_leftTotal = _c0t__tmp_148;
      }
      _c0v_rightTotal = _c0v_newTotal;
    }
    _c0v_parentTotal = ((1 + _c0v_leftTotal) + _c0v_rightTotal);
    int* _c0t__tmp_149;
    _c0t__tmp_149 = &((cc0_deref(struct _c0_Node, _c0v_parent))._c0_total);
    cc0_deref(int, _c0t__tmp_149) = _c0v_parentTotal;
    _c0_fixup_ancestors(_c0v_parent, _c0v_grandparent, _c0v_oldparentTotal, _c0v_parentTotal, _c0v__instanceCounter);
  }
  return 0;
}

int _c0_main() {
  int _c0v_stress = 0;
  int _c0v_stressCaptured = 0;
  int _c0v_seed = 0;
  struct _c0_Node* _c0v_node = NULL;
  int _c0v_i = 0;
  struct _c0_Node* _c0v_current = NULL;
  bool _c0v__ = false;
  bool _c0v__1 = false;
  int _c0v_r = 0;
  bool _c0v_rand_bool = false;
  int _c0v__2 = 0;
  bool _c0v__3 = false;
  bool _c0v__4 = false;
  int _c0v_r1 = 0;
  bool _c0v_rand_bool1 = false;
  int _c0v__5 = 0;
  bool _c0v__6 = false;
  struct _c0_Node* _c0v_current1 = NULL;
  struct _c0_Node* _c0v_current2 = NULL;
  struct _c0_Node* _c0v_current21 = NULL;
  int* _c0v__instanceCounter = NULL;
  int* _c0t__tmp_150 = cc0_alloc(int);
  _c0v__instanceCounter = _c0t__tmp_150;
  _c0v_stress = 0;
  _c0v_stressCaptured = (_c0v_stress + ((_c0v_stress / 2) * 2));
  _c0v_seed = 1;
  struct _c0_Node* _c0t__tmp_151 = _c0_create_tree(_c0v__instanceCounter);
  _c0v_node = _c0t__tmp_151;
  _c0v_i = 0;
  while ((_c0v_i < _c0v_stressCaptured)) {
    _c0v_current = _c0v_node;
    bool _c0t__tmp_152 = _c0_tree_has_left(_c0v_current, _c0v__instanceCounter);
    _c0v__ = _c0t__tmp_152;
    if (_c0v__) {
      bool _c0t__tmp_153 = _c0_tree_has_right(_c0v_current, _c0v__instanceCounter);
      _c0v__1 = _c0t__tmp_153;
    }
    while ((_c0v__ && _c0v__1)) {
      int _c0t__tmp_155 = _c0_rand(_c0v_seed);
      _c0v_r = _c0t__tmp_155;
      _c0v_seed = _c0v_r;
      int _c0t__tmp_156 = _c0_mod(_c0v_seed, _c0v_stressCaptured);
      _c0v__2 = _c0t__tmp_156;
      _c0v_rand_bool = (_c0v__2 <= (_c0v_stressCaptured / 2));
      if (_c0v_rand_bool) {
        struct _c0_Node* _c0t__tmp_157 = _c0_tree_get_left(_c0v_current, _c0v__instanceCounter);
        _c0v_current1 = _c0t__tmp_157;
      } else {
        struct _c0_Node* _c0t__tmp_158 = _c0_tree_get_right(_c0v_current, _c0v__instanceCounter);
        _c0v_current1 = _c0t__tmp_158;
      }
      bool _c0t__tmp_159 = _c0_tree_has_left(_c0v_current1, _c0v__instanceCounter);
      _c0v__ = _c0t__tmp_159;
      if (_c0v__) {
        bool _c0t__tmp_160 = _c0_tree_has_right(_c0v_current1, _c0v__instanceCounter);
        _c0v__1 = _c0t__tmp_160;
      }
      _c0v_current = _c0v_current1;
    }
    bool _c0t__tmp_161 = _c0_tree_has_left(_c0v_current, _c0v__instanceCounter);
    _c0v__3 = _c0t__tmp_161;
    if (_c0v__3) {
      struct _c0_Node* _c0t__tmp_162 = _c0_tree_add_right(_c0v_current, _c0v__instanceCounter);
      _c0v_current2 = _c0t__tmp_162;
    } else {
      bool _c0t__tmp_163 = _c0_tree_has_right(_c0v_current, _c0v__instanceCounter);
      _c0v__4 = _c0t__tmp_163;
      if (_c0v__4) {
        struct _c0_Node* _c0t__tmp_164 = _c0_tree_add_left(_c0v_current, _c0v__instanceCounter);
        _c0v_current2 = _c0t__tmp_164;
      } else {
        int _c0t__tmp_165 = _c0_rand(_c0v_seed);
        _c0v_r1 = _c0t__tmp_165;
        _c0v_seed = _c0v_r1;
        int _c0t__tmp_166 = _c0_mod(_c0v_seed, _c0v_stressCaptured);
        _c0v__5 = _c0t__tmp_166;
        _c0v_rand_bool1 = (_c0v__5 <= (_c0v_stressCaptured / 2));
        if (_c0v_rand_bool1) {
          struct _c0_Node* _c0t__tmp_167 = _c0_tree_add_right(_c0v_current, _c0v__instanceCounter);
          _c0v_current2 = _c0t__tmp_167;
        } else {
          struct _c0_Node* _c0t__tmp_168 = _c0_tree_add_left(_c0v_current, _c0v__instanceCounter);
          _c0v_current2 = _c0t__tmp_168;
        }
      }
    }
    bool _c0t__tmp_169 = _c0_tree_has_parent(_c0v_current2, _c0v__instanceCounter);
    _c0v__6 = _c0t__tmp_169;
    while (_c0v__6) {
      struct _c0_Node* _c0t__tmp_170 = _c0_tree_get_parent(_c0v_current2, _c0v__instanceCounter);
      _c0v_current21 = _c0t__tmp_170;
      bool _c0t__tmp_171 = _c0_tree_has_parent(_c0v_current21, _c0v__instanceCounter);
      _c0v__6 = _c0t__tmp_171;
      _c0v_current2 = _c0v_current21;
    }
    _c0v_node = _c0v_current2;
    _c0v_i = (_c0v_i + 1);
    _c0v_current = _c0v_current2;
  }
  return 0;
}

struct _c0_Node;
struct _c0_Node* _c0_tree_add_left(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter) {
  struct _c0_Node* _c0v_n = NULL;
  struct _c0_Node* _c0v_nodeLeft = NULL;
  if ((_c0v_node == NULL)) {
    return _c0v_node;
  } else {
    struct _c0_Node* _c0t__tmp_172 = cc0_alloc(struct _c0_Node);
    _c0v_n = _c0t__tmp_172;
    int* _c0t__tmp_173;
    _c0t__tmp_173 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0__id);
    int _c0t__tmp_174 = cc0_deref(int, _c0v__instanceCounter);
    cc0_deref(int, _c0t__tmp_173) = _c0t__tmp_174;
    int _c0t__tmp_175 = cc0_deref(int, _c0v__instanceCounter);
    cc0_deref(int, _c0v__instanceCounter) = (_c0t__tmp_175 + 1);
    struct _c0_Node** _c0t__tmp_176;
    _c0t__tmp_176 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_left);
    cc0_deref(struct _c0_Node*, _c0t__tmp_176) = NULL;
    struct _c0_Node** _c0t__tmp_177;
    _c0t__tmp_177 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_right);
    cc0_deref(struct _c0_Node*, _c0t__tmp_177) = NULL;
    struct _c0_Node** _c0t__tmp_178;
    _c0t__tmp_178 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_parent);
    cc0_deref(struct _c0_Node*, _c0t__tmp_178) = _c0v_node;
    int* _c0t__tmp_179;
    _c0t__tmp_179 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_total);
    cc0_deref(int, _c0t__tmp_179) = 1;
    struct _c0_Node* _c0t__tmp_180 = (cc0_deref(struct _c0_Node, _c0v_node))._c0_left;
    _c0v_nodeLeft = _c0t__tmp_180;
    if ((_c0v_nodeLeft != NULL)) {
      return _c0v_node;
    } else {
      struct _c0_Node** _c0t__tmp_181;
      _c0t__tmp_181 = &((cc0_deref(struct _c0_Node, _c0v_node))._c0_left);
      cc0_deref(struct _c0_Node*, _c0t__tmp_181) = _c0v_n;
      _c0_fixup_ancestors(_c0v_n, _c0v_node, 0, 1, _c0v__instanceCounter);
      return _c0v_n;
    }
  }
}

struct _c0_Node;
struct _c0_Node* _c0_tree_add_right(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter) {
  struct _c0_Node* _c0v_n = NULL;
  struct _c0_Node* _c0v_nodeRight = NULL;
  if ((_c0v_node == NULL)) {
    return _c0v_node;
  } else {
    struct _c0_Node* _c0t__tmp_182 = cc0_alloc(struct _c0_Node);
    _c0v_n = _c0t__tmp_182;
    int* _c0t__tmp_183;
    _c0t__tmp_183 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0__id);
    int _c0t__tmp_184 = cc0_deref(int, _c0v__instanceCounter);
    cc0_deref(int, _c0t__tmp_183) = _c0t__tmp_184;
    int _c0t__tmp_185 = cc0_deref(int, _c0v__instanceCounter);
    cc0_deref(int, _c0v__instanceCounter) = (_c0t__tmp_185 + 1);
    struct _c0_Node** _c0t__tmp_186;
    _c0t__tmp_186 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_left);
    cc0_deref(struct _c0_Node*, _c0t__tmp_186) = NULL;
    struct _c0_Node** _c0t__tmp_187;
    _c0t__tmp_187 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_right);
    cc0_deref(struct _c0_Node*, _c0t__tmp_187) = NULL;
    struct _c0_Node** _c0t__tmp_188;
    _c0t__tmp_188 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_parent);
    cc0_deref(struct _c0_Node*, _c0t__tmp_188) = _c0v_node;
    int* _c0t__tmp_189;
    _c0t__tmp_189 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_total);
    cc0_deref(int, _c0t__tmp_189) = 1;
    struct _c0_Node* _c0t__tmp_190 = (cc0_deref(struct _c0_Node, _c0v_node))._c0_right;
    _c0v_nodeRight = _c0t__tmp_190;
    if ((_c0v_nodeRight != NULL)) {
      return _c0v_node;
    } else {
      struct _c0_Node** _c0t__tmp_191;
      _c0t__tmp_191 = &((cc0_deref(struct _c0_Node, _c0v_node))._c0_right);
      cc0_deref(struct _c0_Node*, _c0t__tmp_191) = _c0v_n;
      _c0_fixup_ancestors(_c0v_n, _c0v_node, 0, 1, _c0v__instanceCounter);
      return _c0v_n;
    }
  }
}

struct _c0_Node;
struct _c0_Node* _c0_tree_get_left(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter) {
  struct _c0_Node* _c0v_left = NULL;
  if ((_c0v_node == NULL)) {
    return NULL;
  } else {
    struct _c0_Node* _c0t__tmp_192 = (cc0_deref(struct _c0_Node, _c0v_node))._c0_left;
    _c0v_left = _c0t__tmp_192;
    if ((_c0v_left != NULL)) {
    }
    return _c0v_left;
  }
}

struct _c0_Node;
struct _c0_Node* _c0_tree_get_parent(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter) {
  struct _c0_Node* _c0v_parent = NULL;
  if ((_c0v_node == NULL)) {
    return NULL;
  } else {
    struct _c0_Node* _c0t__tmp_193 = (cc0_deref(struct _c0_Node, _c0v_node))._c0_parent;
    _c0v_parent = _c0t__tmp_193;
    if ((_c0v_parent == NULL)) {
      return NULL;
    } else {
      return _c0v_parent;
    }
  }
}

struct _c0_Node;
struct _c0_Node* _c0_tree_get_right(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter) {
  struct _c0_Node* _c0v_right = NULL;
  if ((_c0v_node == NULL)) {
    return NULL;
  } else {
    struct _c0_Node* _c0t__tmp_194 = (cc0_deref(struct _c0_Node, _c0v_node))._c0_right;
    _c0v_right = _c0t__tmp_194;
    if ((_c0v_right != NULL)) {
    }
    return _c0v_right;
  }
}

struct _c0_Node;
int _c0_tree_get_total(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter) {
  int _c0v_result = 0;
  _c0v_result = 0;
  if ((_c0v_node == NULL)) {
  } else {
    int _c0t__tmp_195 = (cc0_deref(struct _c0_Node, _c0v_node))._c0_total;
    _c0v_result = _c0t__tmp_195;
  }
  return _c0v_result;
}

struct _c0_Node;
bool _c0_tree_has_left(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter) {
  bool _c0v_res = false;
  struct _c0_Node* _c0v_left = NULL;
  _c0v_res = false;
  if ((_c0v_node == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_196 = (cc0_deref(struct _c0_Node, _c0v_node))._c0_left;
    _c0v_left = _c0t__tmp_196;
    _c0v_res = (_c0v_left != NULL);
  }
  return _c0v_res;
}

struct _c0_Node;
bool _c0_tree_has_parent(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter) {
  bool _c0v_res = false;
  struct _c0_Node* _c0v_parent = NULL;
  _c0v_res = false;
  if ((_c0v_node == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_197 = (cc0_deref(struct _c0_Node, _c0v_node))._c0_parent;
    _c0v_parent = _c0t__tmp_197;
    _c0v_res = (_c0v_parent != NULL);
  }
  return _c0v_res;
}

struct _c0_Node;
bool _c0_tree_has_right(struct _c0_Node* _c0v_node, int* _c0v__instanceCounter) {
  bool _c0v_res = false;
  struct _c0_Node* _c0v_right = NULL;
  _c0v_res = false;
  if ((_c0v_node == NULL)) {
  } else {
    struct _c0_Node* _c0t__tmp_198 = (cc0_deref(struct _c0_Node, _c0v_node))._c0_right;
    _c0v_right = _c0t__tmp_198;
    _c0v_res = (_c0v_right != NULL);
  }
  return _c0v_res;
}
long map_length = 900;
const char* source_map[900] = {
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
  [553] = "src/test/resources/runtime-analysis/composite.verified.c0: 31.3-31.9",
  [554] = "src/test/resources/runtime-analysis/composite.verified.c0: 31.12-31.29",
  [555] = "src/test/resources/runtime-analysis/composite.verified.c0: 31.3-31.29",
  [556] = "src/test/resources/runtime-analysis/composite.verified.c0: 32.23-32.40",
  [557] = "src/test/resources/runtime-analysis/composite.verified.c0: 32.3-32.44",
  [559] = "src/test/resources/runtime-analysis/composite.verified.c0: 33.3-33.10",
  [560] = "src/test/resources/runtime-analysis/composite.verified.c0: 33.3-33.17",
  [562] = "src/test/resources/runtime-analysis/composite.verified.c0: 34.3-34.11",
  [563] = "src/test/resources/runtime-analysis/composite.verified.c0: 34.3-34.18",
  [565] = "src/test/resources/runtime-analysis/composite.verified.c0: 35.3-35.12",
  [566] = "src/test/resources/runtime-analysis/composite.verified.c0: 35.3-35.19",
  [568] = "src/test/resources/runtime-analysis/composite.verified.c0: 36.3-36.11",
  [569] = "src/test/resources/runtime-analysis/composite.verified.c0: 36.3-36.15",
  [585] = "src/test/resources/runtime-analysis/composite.verified.c0: 54.12-54.24",
  [587] = "src/test/resources/runtime-analysis/composite.verified.c0: 55.13-55.26",
  [589] = "src/test/resources/runtime-analysis/composite.verified.c0: 56.19-56.33",
  [591] = "src/test/resources/runtime-analysis/composite.verified.c0: 57.22-57.35",
  [598] = "src/test/resources/runtime-analysis/composite.verified.c0: 65.22-65.34",
  [603] = "src/test/resources/runtime-analysis/composite.verified.c0: 72.21-72.32",
  [610] = "src/test/resources/runtime-analysis/composite.verified.c0: 77.5-77.18",
  [611] = "src/test/resources/runtime-analysis/composite.verified.c0: 77.5-77.32",
  [612] = "src/test/resources/runtime-analysis/composite.verified.c0: 78.5-78.88",
  [644] = "src/test/resources/runtime-analysis/composite.verified.c0: 110.10-110.39",
  [649] = "src/test/resources/runtime-analysis/composite.verified.c0: 115.9-115.49",
  [652] = "src/test/resources/runtime-analysis/composite.verified.c0: 118.12-118.53",
  [656] = "src/test/resources/runtime-analysis/composite.verified.c0: 122.11-122.21",
  [659] = "src/test/resources/runtime-analysis/composite.verified.c0: 124.12-124.37",
  [663] = "src/test/resources/runtime-analysis/composite.verified.c0: 128.20-128.60",
  [666] = "src/test/resources/runtime-analysis/composite.verified.c0: 132.20-132.61",
  [669] = "src/test/resources/runtime-analysis/composite.verified.c0: 134.11-134.52",
  [672] = "src/test/resources/runtime-analysis/composite.verified.c0: 137.14-137.56",
  [677] = "src/test/resources/runtime-analysis/composite.verified.c0: 141.10-141.50",
  [680] = "src/test/resources/runtime-analysis/composite.verified.c0: 144.18-144.59",
  [683] = "src/test/resources/runtime-analysis/composite.verified.c0: 148.12-148.53",
  [686] = "src/test/resources/runtime-analysis/composite.verified.c0: 151.20-151.60",
  [689] = "src/test/resources/runtime-analysis/composite.verified.c0: 155.14-155.24",
  [692] = "src/test/resources/runtime-analysis/composite.verified.c0: 157.14-157.39",
  [696] = "src/test/resources/runtime-analysis/composite.verified.c0: 161.22-161.63",
  [699] = "src/test/resources/runtime-analysis/composite.verified.c0: 165.22-165.62",
  [704] = "src/test/resources/runtime-analysis/composite.verified.c0: 169.10-169.53",
  [707] = "src/test/resources/runtime-analysis/composite.verified.c0: 172.19-172.62",
  [709] = "src/test/resources/runtime-analysis/composite.verified.c0: 173.12-173.56",
  [730] = "src/test/resources/runtime-analysis/composite.verified.c0: 194.5-194.11",
  [731] = "src/test/resources/runtime-analysis/composite.verified.c0: 194.14-194.31",
  [732] = "src/test/resources/runtime-analysis/composite.verified.c0: 194.5-194.31",
  [733] = "src/test/resources/runtime-analysis/composite.verified.c0: 195.25-195.42",
  [734] = "src/test/resources/runtime-analysis/composite.verified.c0: 195.5-195.46",
  [736] = "src/test/resources/runtime-analysis/composite.verified.c0: 196.5-196.12",
  [737] = "src/test/resources/runtime-analysis/composite.verified.c0: 196.5-196.19",
  [739] = "src/test/resources/runtime-analysis/composite.verified.c0: 197.5-197.13",
  [740] = "src/test/resources/runtime-analysis/composite.verified.c0: 197.5-197.20",
  [742] = "src/test/resources/runtime-analysis/composite.verified.c0: 198.5-198.14",
  [743] = "src/test/resources/runtime-analysis/composite.verified.c0: 198.5-198.21",
  [745] = "src/test/resources/runtime-analysis/composite.verified.c0: 199.5-199.13",
  [746] = "src/test/resources/runtime-analysis/composite.verified.c0: 199.5-199.17",
  [747] = "src/test/resources/runtime-analysis/composite.verified.c0: 200.16-200.26",
  [753] = "src/test/resources/runtime-analysis/composite.verified.c0: 207.7-207.17",
  [754] = "src/test/resources/runtime-analysis/composite.verified.c0: 207.7-207.21",
  [755] = "src/test/resources/runtime-analysis/composite.verified.c0: 208.7-208.55",
  [771] = "src/test/resources/runtime-analysis/composite.verified.c0: 225.5-225.11",
  [772] = "src/test/resources/runtime-analysis/composite.verified.c0: 225.14-225.31",
  [773] = "src/test/resources/runtime-analysis/composite.verified.c0: 225.5-225.31",
  [774] = "src/test/resources/runtime-analysis/composite.verified.c0: 226.25-226.42",
  [775] = "src/test/resources/runtime-analysis/composite.verified.c0: 226.5-226.46",
  [777] = "src/test/resources/runtime-analysis/composite.verified.c0: 227.5-227.12",
  [778] = "src/test/resources/runtime-analysis/composite.verified.c0: 227.5-227.19",
  [780] = "src/test/resources/runtime-analysis/composite.verified.c0: 228.5-228.13",
  [781] = "src/test/resources/runtime-analysis/composite.verified.c0: 228.5-228.20",
  [783] = "src/test/resources/runtime-analysis/composite.verified.c0: 229.5-229.14",
  [784] = "src/test/resources/runtime-analysis/composite.verified.c0: 229.5-229.21",
  [786] = "src/test/resources/runtime-analysis/composite.verified.c0: 230.5-230.13",
  [787] = "src/test/resources/runtime-analysis/composite.verified.c0: 230.5-230.17",
  [788] = "src/test/resources/runtime-analysis/composite.verified.c0: 231.17-231.28",
  [794] = "src/test/resources/runtime-analysis/composite.verified.c0: 238.7-238.18",
  [795] = "src/test/resources/runtime-analysis/composite.verified.c0: 238.7-238.22",
  [796] = "src/test/resources/runtime-analysis/composite.verified.c0: 239.7-239.55",
  [808] = "src/test/resources/runtime-analysis/composite.verified.c0: 254.12-254.22",
  [822] = "src/test/resources/runtime-analysis/composite.verified.c0: 271.14-271.26",
  [838] = "src/test/resources/runtime-analysis/composite.verified.c0: 292.13-292.24",
  [852] = "src/test/resources/runtime-analysis/composite.verified.c0: 309.14-309.25",
  [865] = "src/test/resources/runtime-analysis/composite.verified.c0: 324.12-324.22",
  [879] = "src/test/resources/runtime-analysis/composite.verified.c0: 340.14-340.26",
  [893] = "src/test/resources/runtime-analysis/composite.verified.c0: 356.13-356.24"
};
