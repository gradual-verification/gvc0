#include "cc0lib.h"
#include "c0rt.h"
#include "list.verified.c0.h"

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
struct _c0_Node;
struct _c0_Node {
  int _c0_val;
  struct _c0_Node* _c0_next;
  int _c0__id;
};
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_sorted(struct _c0_Node* _c0v_list, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_sortedSeg(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_sortedSegHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_prev, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_Node;
struct _c0_Node;
void _c0_appendLemmaAfterLoopBody(struct _c0_Node* _c0v_a, struct _c0_Node* _c0v_b, struct _c0_Node* _c0v_c, int _c0v_aPrev, int _c0v_bVal, int _c0v_cVal, int* _c0v__instanceCounter);
struct _c0_Node;
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_appendLemmaLoopBody(struct _c0_Node* _c0v_a, struct _c0_Node* _c0v_b, struct _c0_Node* _c0v_c, int _c0v_aPrev, int _c0v_cPrev, int _c0v_bVal, int _c0v_cVal, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node* _c0_create_list(int _c0v_val, int* _c0v__instanceCounter);
struct _c0_Node;
struct _c0_OwnedFields;
struct _c0_Node* _c0_list_insert(struct _c0_Node* _c0v_list, int _c0v_val, struct _c0_OwnedFields* _c0v__ownedFields);
int _c0_main();
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sortedSegHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_prev, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields);

struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_sorted(struct _c0_Node* _c0v_list, struct _c0_OwnedFields* _c0v__ownedFields) {
  _c0_add_sortedSeg(_c0v_list, NULL, -(1), _c0v__ownedFields);
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_sortedSeg(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields) {
  if (!((_c0v_start == _c0v_end))) {
    int _c0t__tmp_117 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_addAcc(_c0v__ownedFields, _c0t__tmp_117, 3, 0);
    int _c0t__tmp_118 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_addAcc(_c0v__ownedFields, _c0t__tmp_118, 3, 1);
    struct _c0_Node* _c0t__tmp_119 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    int _c0t__tmp_120 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_val;
    _c0_add_sortedSegHelper(_c0t__tmp_119, _c0v_end, _c0t__tmp_120, _c0v_endVal, _c0v__ownedFields);
  }
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_add_sortedSegHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_prev, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields) {
  if (!((_c0v_start == _c0v_end))) {
    int _c0t__tmp_121 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_addAcc(_c0v__ownedFields, _c0t__tmp_121, 3, 0);
    int _c0t__tmp_122 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_addAcc(_c0v__ownedFields, _c0t__tmp_122, 3, 1);
    struct _c0_Node* _c0t__tmp_123 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    int _c0t__tmp_124 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_val;
    _c0_add_sortedSegHelper(_c0t__tmp_123, _c0v_end, _c0t__tmp_124, _c0v_endVal, _c0v__ownedFields);
  }
}

struct _c0_Node;
struct _c0_Node;
struct _c0_Node;
void _c0_appendLemmaAfterLoopBody(struct _c0_Node* _c0v_a, struct _c0_Node* _c0v_b, struct _c0_Node* _c0v_c, int _c0v_aPrev, int _c0v_bVal, int _c0v_cVal, int* _c0v__instanceCounter) {
  if ((_c0v_b == _c0v_c)) {
  } else {
    if ((_c0v_a == _c0v_b)) {
    } else {
      struct _c0_Node* _c0t__tmp_125 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_next;
      int _c0t__tmp_126 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_val;
      _c0_appendLemmaAfterLoopBody(_c0t__tmp_125, _c0v_b, _c0v_c, _c0t__tmp_126, _c0v_bVal, _c0v_cVal, _c0v__instanceCounter);
    }
  }
}

struct _c0_Node;
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_appendLemmaLoopBody(struct _c0_Node* _c0v_a, struct _c0_Node* _c0v_b, struct _c0_Node* _c0v_c, int _c0v_aPrev, int _c0v_cPrev, int _c0v_bVal, int _c0v_cVal, struct _c0_OwnedFields* _c0v__ownedFields) {
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
  struct _c0_OwnedFields* _c0v__tempFields1 = NULL;
  _c0v__cond_1 = (_c0v_b == _c0v_c);
  _c0v__cond_2 = (_c0v_c == NULL);
  if ((_c0v_b == _c0v_c)) {
  } else {
    _c0v__cond_3 = (_c0v_a == _c0v_b);
    if ((_c0v_a == _c0v_b)) {
      _c0v__cond_4 = (_c0v_b == _c0v_a);
      _c0v__cond_5 = (_c0v_a == NULL);
      if ((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !((_c0v_b == _c0v_c))) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !((_c0v_b == _c0v_c)))) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !((_c0v_b == _c0v_c)))) || ((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !((_c0v_b == _c0v_c)))) || ((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !((_c0v_b == _c0v_c)))) || ((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !((_c0v_b == _c0v_c))))) {
        int _c0t__tmp_193;
        if ((_c0v_b != NULL)) {
          int _c0t__tmp_192 = (cc0_deref(struct _c0_Node, _c0v_b))._c0__id;
          _c0t__tmp_193 = _c0t__tmp_192;
        } else {
          _c0t__tmp_193 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_193, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
      }
      if ((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !((_c0v_b == _c0v_c))) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !((_c0v_b == _c0v_c)))) || ((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !((_c0v_b == _c0v_c)))) || ((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !((_c0v_b == _c0v_c))))) {
        int _c0t__tmp_238;
        if ((_c0v_b != NULL)) {
          int _c0t__tmp_237 = (cc0_deref(struct _c0_Node, _c0v_b))._c0__id;
          _c0t__tmp_238 = _c0t__tmp_237;
        } else {
          _c0t__tmp_238 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_238, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
      }
      if ((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !((_c0v_b == _c0v_c))) || ((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !((_c0v_b == _c0v_c))))) {
        int _c0t__tmp_260 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_val;
        cc0_assert((_c0t__tmp_260 >= _c0v_aPrev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 100.9-100.33: assert failed"));
        struct _c0_Node* _c0t__tmp_261 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_next;
        int _c0t__tmp_262 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_val;
        _c0_sortedSegHelper(_c0t__tmp_261, _c0v_c, _c0t__tmp_262, _c0v_cVal, _c0v__ownedFields);
      }
      _c0v__cond_11 = (_c0v_b == _c0v_c);
    } else {
      _c0v__cond_6 = (_c0v_a == _c0v_b);
      int* _c0t__tmp_263 = (cc0_deref(struct _c0_OwnedFields, _c0v__ownedFields))._c0_instanceCounter;
      struct _c0_OwnedFields* _c0t__tmp_264 = _c0_initOwnedFields(_c0t__tmp_263);
      _c0v__tempFields = _c0t__tmp_264;
      if (((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && !((_c0v_c == NULL)))) {
        int _c0t__tmp_276;
        if ((_c0v_c != NULL)) {
          int _c0t__tmp_275 = (cc0_deref(struct _c0_Node, _c0v_c))._c0__id;
          _c0t__tmp_276 = _c0t__tmp_275;
        } else {
          _c0t__tmp_276 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_276, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
      }
      if (((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && !((_c0v_c == NULL))) && !((_c0v_b == _c0v_c))) || (((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && (_c0v_c == NULL)) && !((_c0v_b == _c0v_c))))) {
        int _c0t__tmp_301;
        if ((_c0v_b != NULL)) {
          int _c0t__tmp_300 = (cc0_deref(struct _c0_Node, _c0v_b))._c0__id;
          _c0t__tmp_301 = _c0t__tmp_300;
        } else {
          _c0t__tmp_301 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_301, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
      }
      if (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && !((_c0v_c == NULL))) && !((_c0v_b == _c0v_c))) || (((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && !((_c0v_c == NULL))) && !((_c0v_b == _c0v_c)))) || (((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && (_c0v_c == NULL)) && !((_c0v_b == _c0v_c)))) || (((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && (_c0v_c == NULL)) && !((_c0v_b == _c0v_c))))) {
        int _c0t__tmp_350;
        if ((_c0v_b != NULL)) {
          int _c0t__tmp_349 = (cc0_deref(struct _c0_Node, _c0v_b))._c0__id;
          _c0t__tmp_350 = _c0t__tmp_349;
        } else {
          _c0t__tmp_350 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_350, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
      }
      if (((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && !((_c0v_c == NULL))) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && !((_c0v_c == NULL)))) || ((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && !((_c0v_c == NULL))))) {
        int _c0t__tmp_384;
        if ((_c0v_c != NULL)) {
          int _c0t__tmp_383 = (cc0_deref(struct _c0_Node, _c0v_c))._c0__id;
          _c0t__tmp_384 = _c0t__tmp_383;
        } else {
          _c0t__tmp_384 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_384, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
      }
      if (((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && !((_c0v_c == NULL)))) {
        cc0_assert((_c0v_cVal == _c0v_cVal), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 127.9-127.30: assert failed"));
        int _c0t__tmp_395 = (cc0_deref(struct _c0_Node, _c0v_c))._c0_val;
        cc0_assert((_c0t__tmp_395 >= _c0v_cPrev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 128.9-128.33: assert failed"));
      }
      if (((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && !((_c0v_c == NULL))) && !((_c0v_b == _c0v_c))) || (((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && (_c0v_c == NULL)) && !((_c0v_b == _c0v_c))))) {
        cc0_assert((_c0v_bVal == _c0v_bVal), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 132.9-132.30: assert failed"));
      }
      if (!((_c0v_c == NULL))) {
        int _c0t__tmp_420;
        if ((_c0v_c != NULL)) {
          int _c0t__tmp_419 = (cc0_deref(struct _c0_Node, _c0v_c))._c0__id;
          _c0t__tmp_420 = _c0t__tmp_419;
        } else {
          _c0t__tmp_420 = -(1);
        }
        _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_420, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
        int _c0t__tmp_422;
        if ((_c0v_c != NULL)) {
          int _c0t__tmp_421 = (cc0_deref(struct _c0_Node, _c0v_c))._c0__id;
          _c0t__tmp_422 = _c0t__tmp_421;
        } else {
          _c0t__tmp_422 = -(1);
        }
        _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_422, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
      }
      if (!((_c0v_b == _c0v_c))) {
        int _c0t__tmp_424;
        if ((_c0v_b != NULL)) {
          int _c0t__tmp_423 = (cc0_deref(struct _c0_Node, _c0v_b))._c0__id;
          _c0t__tmp_424 = _c0t__tmp_423;
        } else {
          _c0t__tmp_424 = -(1);
        }
        _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_424, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
        int _c0t__tmp_426;
        if ((_c0v_b != NULL)) {
          int _c0t__tmp_425 = (cc0_deref(struct _c0_Node, _c0v_b))._c0__id;
          _c0t__tmp_426 = _c0t__tmp_425;
        } else {
          _c0t__tmp_426 = -(1);
        }
        _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_426, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
      }
      _c0v__cond_7 = (_c0v_b == _c0v_c);
      _c0v__cond_8 = (_c0v_c == NULL);
      struct _c0_Node* _c0t__tmp_427 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_next;
      int _c0t__tmp_428 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_val;
      _c0_appendLemmaLoopBody(_c0t__tmp_427, _c0v_b, _c0v_c, _c0t__tmp_428, _c0v_cPrev, _c0v_bVal, _c0v_cVal, _c0v__ownedFields);
      if (((((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && !(_c0v__cond_8)) && !(_c0v__cond_7)) && !((_c0v_c == NULL))) && !((_c0v_a == _c0v_c))) || (((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && !(_c0v__cond_8)) && !(_c0v__cond_7)) && !((_c0v_c == NULL))) && !((_c0v_a == _c0v_c)))) || (((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && !(_c0v__cond_8)) && !(_c0v__cond_7)) && !((_c0v_c == NULL))) && !((_c0v_a == _c0v_c)))) || (((((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_7)) && (_c0v_c == NULL)) && !((_c0v_a == _c0v_c)))) || (((((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_7)) && (_c0v_c == NULL)) && !((_c0v_a == _c0v_c)))) || (((((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_7)) && (_c0v_c == NULL)) && !((_c0v_a == _c0v_c))))) {
        int _c0t__tmp_513;
        if ((_c0v_a != NULL)) {
          int _c0t__tmp_512 = (cc0_deref(struct _c0_Node, _c0v_a))._c0__id;
          _c0t__tmp_513 = _c0t__tmp_512;
        } else {
          _c0t__tmp_513 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_513, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
      }
      if (((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && !(_c0v__cond_8)) && !(_c0v__cond_7)) && !((_c0v_c == NULL))) && !((_c0v_a == _c0v_c))) || (((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && !(_c0v__cond_8)) && !(_c0v__cond_7)) && !((_c0v_c == NULL))) && !((_c0v_a == _c0v_c)))) || (((((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_7)) && (_c0v_c == NULL)) && !((_c0v_a == _c0v_c)))) || (((((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_7)) && (_c0v_c == NULL)) && !((_c0v_a == _c0v_c))))) {
        int _c0t__tmp_570;
        if ((_c0v_a != NULL)) {
          int _c0t__tmp_569 = (cc0_deref(struct _c0_Node, _c0v_a))._c0__id;
          _c0t__tmp_570 = _c0t__tmp_569;
        } else {
          _c0t__tmp_570 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_570, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
      }
      if (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && !(_c0v__cond_8)) && !(_c0v__cond_7)) && !((_c0v_c == NULL))) && !((_c0v_a == _c0v_c))) || (((((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_7)) && (_c0v_c == NULL)) && !((_c0v_a == _c0v_c))))) {
        int _c0t__tmp_598 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_val;
        cc0_assert((_c0t__tmp_598 >= _c0v_aPrev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 157.9-157.33: assert failed"));
        struct _c0_Node* _c0t__tmp_599 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_next;
        int _c0t__tmp_600 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_val;
        _c0_sortedSegHelper(_c0t__tmp_599, _c0v_c, _c0t__tmp_600, _c0v_cVal, _c0v__ownedFields);
      }
      if (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && !(_c0v__cond_8)) && !(_c0v__cond_7)) && !((_c0v_c == NULL))) && (_c0v_a == _c0v_c)) && !((_c0v_a == NULL)))) {
        cc0_assert((_c0v_cVal >= _c0v_aPrev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 162.9-162.31: assert failed"));
      }
      _c0v__cond_9 = (_c0v_c == NULL);
      _c0v__cond_10 = (_c0v_a == _c0v_c);
    }
  }
  int* _c0t__tmp_615 = (cc0_deref(struct _c0_OwnedFields, _c0v__ownedFields))._c0_instanceCounter;
  struct _c0_OwnedFields* _c0t__tmp_616 = _c0_initOwnedFields(_c0t__tmp_615);
  _c0v__tempFields1 = _c0t__tmp_616;
  if ((((((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && !(_c0v__cond_8)) && !(_c0v__cond_7)) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !((_c0v_c == NULL))) || (((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_11)) && !((_c0v_c == NULL)))) || ((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && !(_c0v__cond_8)) && !(_c0v__cond_7)) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !((_c0v_c == NULL)))) || (((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_11)) && !((_c0v_c == NULL)))) || ((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && !(_c0v__cond_8)) && !(_c0v__cond_7)) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !((_c0v_c == NULL)))) || (((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_11)) && !((_c0v_c == NULL))))) {
    int _c0t__tmp_698;
    if ((_c0v_c != NULL)) {
      int _c0t__tmp_697 = (cc0_deref(struct _c0_Node, _c0v_c))._c0__id;
      _c0t__tmp_698 = _c0t__tmp_697;
    } else {
      _c0t__tmp_698 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_698, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
  }
  if ((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && !(_c0v__cond_8)) && !(_c0v__cond_7)) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !((_c0v_c == NULL))) || (((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_3) && _c0v__cond_4) && !(_c0v__cond_5)) && !(_c0v__cond_11)) && !((_c0v_c == NULL))))) {
    int _c0t__tmp_726;
    if ((_c0v_c != NULL)) {
      int _c0t__tmp_725 = (cc0_deref(struct _c0_Node, _c0v_c))._c0__id;
      _c0t__tmp_726 = _c0t__tmp_725;
    } else {
      _c0t__tmp_726 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_726, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
    cc0_assert((_c0v_cVal == _c0v_cVal), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 176.5-176.26: assert failed"));
    int _c0t__tmp_727 = (cc0_deref(struct _c0_Node, _c0v_c))._c0_val;
    cc0_assert((_c0t__tmp_727 >= _c0v_cPrev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 177.5-177.29: assert failed"));
  }
  if (!((_c0v_c == NULL))) {
    int _c0t__tmp_729;
    if ((_c0v_c != NULL)) {
      int _c0t__tmp_728 = (cc0_deref(struct _c0_Node, _c0v_c))._c0__id;
      _c0t__tmp_729 = _c0t__tmp_728;
    } else {
      _c0t__tmp_729 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__tempFields1, _c0t__tmp_729, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
    int _c0t__tmp_731;
    if ((_c0v_c != NULL)) {
      int _c0t__tmp_730 = (cc0_deref(struct _c0_Node, _c0v_c))._c0__id;
      _c0t__tmp_731 = _c0t__tmp_730;
    } else {
      _c0t__tmp_731 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__tempFields1, _c0t__tmp_731, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
  }
}

struct _c0_Node* _c0_create_list(int _c0v_val, int* _c0v__instanceCounter) {
  struct _c0_Node* _c0v_n = NULL;
  struct _c0_Node* _c0t__tmp_732 = cc0_alloc(struct _c0_Node);
  _c0v_n = _c0t__tmp_732;
  int* _c0t__tmp_733;
  _c0t__tmp_733 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0__id);
  int _c0t__tmp_734 = cc0_deref(int, _c0v__instanceCounter);
  cc0_deref(int, _c0t__tmp_733) = _c0t__tmp_734;
  int _c0t__tmp_735 = cc0_deref(int, _c0v__instanceCounter);
  cc0_deref(int, _c0v__instanceCounter) = (_c0t__tmp_735 + 1);
  int* _c0t__tmp_736;
  _c0t__tmp_736 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_val);
  cc0_deref(int, _c0t__tmp_736) = _c0v_val;
  struct _c0_Node** _c0t__tmp_737;
  _c0t__tmp_737 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_next);
  cc0_deref(struct _c0_Node*, _c0t__tmp_737) = NULL;
  return _c0v_n;
}

struct _c0_Node;
struct _c0_OwnedFields;
struct _c0_Node* _c0_list_insert(struct _c0_Node* _c0v_list, int _c0v_val, struct _c0_OwnedFields* _c0v__ownedFields) {
  struct _c0_Node* _c0v_n = NULL;
  struct _c0_Node* _c0v_curr = NULL;
  struct _c0_Node* _c0v_tmp = NULL;
  struct _c0_Node* _c0v_prev = NULL;
  if ((!((_c0v_list == NULL)) || !((_c0v_list == NULL)))) {
    int _c0t__tmp_740;
    if ((_c0v_list != NULL)) {
      int _c0t__tmp_739 = (cc0_deref(struct _c0_Node, _c0v_list))._c0__id;
      _c0t__tmp_740 = _c0t__tmp_739;
    } else {
      _c0t__tmp_740 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_740, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
  }
  bool _c0t__tmp_742;
  if ((_c0v_list == NULL)) {
    _c0t__tmp_742 = true;
  } else {
    int _c0t__tmp_741 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_val;
    _c0t__tmp_742 = (_c0v_val <= _c0t__tmp_741);
  }
  cc0_assert(_c0t__tmp_742, c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 207.3-207.44: assert failed"));
  bool _c0t__tmp_744;
  if ((_c0v_list == NULL)) {
    _c0t__tmp_744 = true;
  } else {
    int _c0t__tmp_743 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_val;
    _c0t__tmp_744 = (_c0v_val <= _c0t__tmp_743);
  }
  if (_c0t__tmp_744) {
    struct _c0_Node* _c0t__tmp_745 = cc0_alloc(struct _c0_Node);
    _c0v_n = _c0t__tmp_745;
    int* _c0t__tmp_746;
    _c0t__tmp_746 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0__id);
    int _c0t__tmp_747 = _c0_addStructAcc(_c0v__ownedFields, 3);
    cc0_deref(int, _c0t__tmp_746) = _c0t__tmp_747;
    int* _c0t__tmp_748;
    _c0t__tmp_748 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_val);
    cc0_deref(int, _c0t__tmp_748) = _c0v_val;
    struct _c0_Node** _c0t__tmp_749;
    _c0t__tmp_749 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_next);
    cc0_deref(struct _c0_Node*, _c0t__tmp_749) = _c0v_list;
    return _c0v_n;
  } else {
    _c0v_curr = _c0v_list;
    while (true) {
      bool _c0t__tmp_753;
      struct _c0_Node* _c0t__tmp_750 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      if ((_c0t__tmp_750 != NULL)) {
        struct _c0_Node* _c0t__tmp_751 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        int _c0t__tmp_752 = (cc0_deref(struct _c0_Node, _c0t__tmp_751))._c0_val;
        _c0t__tmp_753 = (_c0t__tmp_752 < _c0v_val);
      } else {
        _c0t__tmp_753 = false;
      }
      if (_c0t__tmp_753) {
      } else {
        break;
      }
      _c0v_prev = _c0v_curr;
      struct _c0_Node* _c0t__tmp_754 = (cc0_deref(struct _c0_Node, _c0v_prev))._c0_next;
      _c0v_curr = _c0t__tmp_754;
      if ((_c0v_list == _c0v_prev)) {
      }
    }
    struct _c0_Node* _c0t__tmp_755 = cc0_alloc(struct _c0_Node);
    _c0v_tmp = _c0t__tmp_755;
    int* _c0t__tmp_756;
    _c0t__tmp_756 = &((cc0_deref(struct _c0_Node, _c0v_tmp))._c0__id);
    int _c0t__tmp_757 = _c0_addStructAcc(_c0v__ownedFields, 3);
    cc0_deref(int, _c0t__tmp_756) = _c0t__tmp_757;
    int* _c0t__tmp_758;
    _c0t__tmp_758 = &((cc0_deref(struct _c0_Node, _c0v_tmp))._c0_val);
    cc0_deref(int, _c0t__tmp_758) = _c0v_val;
    struct _c0_Node** _c0t__tmp_759;
    _c0t__tmp_759 = &((cc0_deref(struct _c0_Node, _c0v_tmp))._c0_next);
    struct _c0_Node* _c0t__tmp_760 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
    cc0_deref(struct _c0_Node*, _c0t__tmp_759) = _c0t__tmp_760;
    struct _c0_Node** _c0t__tmp_761;
    _c0t__tmp_761 = &((cc0_deref(struct _c0_Node, _c0v_curr))._c0_next);
    cc0_deref(struct _c0_Node*, _c0t__tmp_761) = _c0v_tmp;
    if ((_c0v_list == _c0v_curr)) {
    }
    return _c0v_list;
  }
}

int _c0_main() {
  int _c0v_stress = 0;
  struct _c0_Node* _c0v_l = NULL;
  int _c0v_i = 0;
  struct _c0_Node* _c0v_l1 = NULL;
  int* _c0v__instanceCounter = NULL;
  struct _c0_OwnedFields* _c0v__ownedFields = NULL;
  int* _c0t__tmp_762 = cc0_alloc(int);
  _c0v__instanceCounter = _c0t__tmp_762;
  struct _c0_OwnedFields* _c0t__tmp_763 = _c0_initOwnedFields(_c0v__instanceCounter);
  _c0v__ownedFields = _c0t__tmp_763;
  _c0v_stress = 0;
  struct _c0_Node* _c0t__tmp_764 = _c0_create_list(3, _c0v__instanceCounter);
  _c0v_l = _c0t__tmp_764;
  _c0_add_sorted(_c0v_l, _c0v__ownedFields);
  _c0v_i = 0;
  while ((_c0v_i < _c0v_stress)) {
    struct _c0_Node* _c0t__tmp_765 = _c0_list_insert(_c0v_l, 1, _c0v__ownedFields);
    _c0v_l1 = _c0t__tmp_765;
    _c0v_i = (_c0v_i + 1);
    _c0v_l = _c0v_l1;
  }
  return 0;
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sortedSegHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_prev, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields) {
  if ((_c0v_start == _c0v_end)) {
    if ((_c0v_end == NULL)) {
      cc0_assert(true, c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 274.7-274.20: assert failed"));
    } else {
      cc0_assert((_c0v_endVal >= _c0v_prev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 278.7-278.30: assert failed"));
    }
  } else {
    int _c0t__tmp_767;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_766 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_767 = _c0t__tmp_766;
    } else {
      _c0t__tmp_767 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_767, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
    int _c0t__tmp_769;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_768 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_769 = _c0t__tmp_768;
    } else {
      _c0t__tmp_769 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_769, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
    int _c0t__tmp_770 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_val;
    cc0_assert((_c0t__tmp_770 >= _c0v_prev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 285.5-285.32: assert failed"));
    struct _c0_Node* _c0t__tmp_771 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    int _c0t__tmp_772 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_val;
    _c0_sortedSegHelper(_c0t__tmp_771, _c0v_end, _c0t__tmp_772, _c0v_endVal, _c0v__ownedFields);
  }
}
long map_length = 904;
const char* source_map[904] = {
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
  [459] = "src/test/resources/runtime-analysis/list.verified.c0: 23.3-23.46",
  [467] = "src/test/resources/runtime-analysis/list.verified.c0: 30.26-30.36",
  [468] = "src/test/resources/runtime-analysis/list.verified.c0: 30.5-30.43",
  [469] = "src/test/resources/runtime-analysis/list.verified.c0: 31.26-31.36",
  [470] = "src/test/resources/runtime-analysis/list.verified.c0: 31.5-31.43",
  [471] = "src/test/resources/runtime-analysis/list.verified.c0: 32.25-32.36",
  [472] = "src/test/resources/runtime-analysis/list.verified.c0: 32.43-32.53",
  [473] = "src/test/resources/runtime-analysis/list.verified.c0: 32.5-32.76",
  [482] = "src/test/resources/runtime-analysis/list.verified.c0: 40.26-40.36",
  [483] = "src/test/resources/runtime-analysis/list.verified.c0: 40.5-40.43",
  [484] = "src/test/resources/runtime-analysis/list.verified.c0: 41.26-41.36",
  [485] = "src/test/resources/runtime-analysis/list.verified.c0: 41.5-41.43",
  [486] = "src/test/resources/runtime-analysis/list.verified.c0: 42.25-42.36",
  [487] = "src/test/resources/runtime-analysis/list.verified.c0: 42.43-42.53",
  [488] = "src/test/resources/runtime-analysis/list.verified.c0: 42.5-42.76",
  [500] = "src/test/resources/runtime-analysis/list.verified.c0: 58.32-58.39",
  [501] = "src/test/resources/runtime-analysis/list.verified.c0: 58.47-58.53",
  [502] = "src/test/resources/runtime-analysis/list.verified.c0: 58.7-58.84",
  [536] = "src/test/resources/runtime-analysis/list.verified.c0: 92.45-92.51",
  [541] = "src/test/resources/runtime-analysis/list.verified.c0: 92.9-92.117",
  [546] = "src/test/resources/runtime-analysis/list.verified.c0: 96.45-96.51",
  [551] = "src/test/resources/runtime-analysis/list.verified.c0: 96.9-96.118",
  [554] = "src/test/resources/runtime-analysis/list.verified.c0: 100.16-100.22",
  [555] = "src/test/resources/runtime-analysis/list.verified.c0: 100.9-100.33",
  [556] = "src/test/resources/runtime-analysis/list.verified.c0: 101.25-101.32",
  [557] = "src/test/resources/runtime-analysis/list.verified.c0: 101.37-101.43",
  [558] = "src/test/resources/runtime-analysis/list.verified.c0: 101.9-101.64",
  [563] = "src/test/resources/runtime-analysis/list.verified.c0: 108.37-108.66",
  [564] = "src/test/resources/runtime-analysis/list.verified.c0: 108.21-108.67",
  [569] = "src/test/resources/runtime-analysis/list.verified.c0: 111.45-111.51",
  [574] = "src/test/resources/runtime-analysis/list.verified.c0: 111.9-111.118",
  [579] = "src/test/resources/runtime-analysis/list.verified.c0: 115.45-115.51",
  [584] = "src/test/resources/runtime-analysis/list.verified.c0: 115.9-115.118",
  [589] = "src/test/resources/runtime-analysis/list.verified.c0: 119.45-119.51",
  [594] = "src/test/resources/runtime-analysis/list.verified.c0: 119.9-119.117",
  [599] = "src/test/resources/runtime-analysis/list.verified.c0: 123.45-123.51",
  [604] = "src/test/resources/runtime-analysis/list.verified.c0: 123.9-123.117",
  [607] = "src/test/resources/runtime-analysis/list.verified.c0: 127.9-127.30",
  [608] = "src/test/resources/runtime-analysis/list.verified.c0: 128.16-128.22",
  [609] = "src/test/resources/runtime-analysis/list.verified.c0: 128.9-128.33",
  [612] = "src/test/resources/runtime-analysis/list.verified.c0: 132.9-132.30",
  [617] = "src/test/resources/runtime-analysis/list.verified.c0: 136.55-136.61",
  [622] = "src/test/resources/runtime-analysis/list.verified.c0: 136.9-136.126",
  [625] = "src/test/resources/runtime-analysis/list.verified.c0: 137.55-137.61",
  [630] = "src/test/resources/runtime-analysis/list.verified.c0: 137.9-137.127",
  [635] = "src/test/resources/runtime-analysis/list.verified.c0: 141.55-141.61",
  [640] = "src/test/resources/runtime-analysis/list.verified.c0: 141.9-141.126",
  [643] = "src/test/resources/runtime-analysis/list.verified.c0: 142.55-142.61",
  [648] = "src/test/resources/runtime-analysis/list.verified.c0: 142.9-142.127",
  [652] = "src/test/resources/runtime-analysis/list.verified.c0: 146.27-146.34",
  [653] = "src/test/resources/runtime-analysis/list.verified.c0: 146.42-146.48",
  [654] = "src/test/resources/runtime-analysis/list.verified.c0: 146.7-146.82",
  [658] = "src/test/resources/runtime-analysis/list.verified.c0: 149.45-149.51",
  [663] = "src/test/resources/runtime-analysis/list.verified.c0: 149.9-149.117",
  [668] = "src/test/resources/runtime-analysis/list.verified.c0: 153.45-153.51",
  [673] = "src/test/resources/runtime-analysis/list.verified.c0: 153.9-153.118",
  [676] = "src/test/resources/runtime-analysis/list.verified.c0: 157.16-157.22",
  [677] = "src/test/resources/runtime-analysis/list.verified.c0: 157.9-157.33",
  [678] = "src/test/resources/runtime-analysis/list.verified.c0: 158.25-158.32",
  [679] = "src/test/resources/runtime-analysis/list.verified.c0: 158.37-158.43",
  [680] = "src/test/resources/runtime-analysis/list.verified.c0: 158.9-158.64",
  [683] = "src/test/resources/runtime-analysis/list.verified.c0: 162.9-162.31",
  [689] = "src/test/resources/runtime-analysis/list.verified.c0: 168.34-168.63",
  [690] = "src/test/resources/runtime-analysis/list.verified.c0: 168.18-168.64",
  [695] = "src/test/resources/runtime-analysis/list.verified.c0: 171.41-171.47",
  [700] = "src/test/resources/runtime-analysis/list.verified.c0: 171.5-171.113",
  [705] = "src/test/resources/runtime-analysis/list.verified.c0: 175.41-175.47",
  [710] = "src/test/resources/runtime-analysis/list.verified.c0: 175.5-175.114",
  [711] = "src/test/resources/runtime-analysis/list.verified.c0: 176.5-176.26",
  [712] = "src/test/resources/runtime-analysis/list.verified.c0: 177.12-177.18",
  [713] = "src/test/resources/runtime-analysis/list.verified.c0: 177.5-177.29",
  [718] = "src/test/resources/runtime-analysis/list.verified.c0: 181.52-181.58",
  [723] = "src/test/resources/runtime-analysis/list.verified.c0: 181.5-181.123",
  [726] = "src/test/resources/runtime-analysis/list.verified.c0: 182.52-182.58",
  [731] = "src/test/resources/runtime-analysis/list.verified.c0: 182.5-182.124",
  [740] = "src/test/resources/runtime-analysis/list.verified.c0: 190.3-190.9",
  [741] = "src/test/resources/runtime-analysis/list.verified.c0: 190.12-190.29",
  [742] = "src/test/resources/runtime-analysis/list.verified.c0: 190.3-190.29",
  [743] = "src/test/resources/runtime-analysis/list.verified.c0: 191.23-191.40",
  [744] = "src/test/resources/runtime-analysis/list.verified.c0: 191.3-191.44",
  [746] = "src/test/resources/runtime-analysis/list.verified.c0: 192.3-192.9",
  [747] = "src/test/resources/runtime-analysis/list.verified.c0: 192.3-192.15",
  [749] = "src/test/resources/runtime-analysis/list.verified.c0: 193.3-193.10",
  [750] = "src/test/resources/runtime-analysis/list.verified.c0: 193.3-193.17",
  [764] = "src/test/resources/runtime-analysis/list.verified.c0: 205.44-205.53",
  [769] = "src/test/resources/runtime-analysis/list.verified.c0: 205.5-205.119",
  [775] = "src/test/resources/runtime-analysis/list.verified.c0: 207.33-207.42",
  [778] = "src/test/resources/runtime-analysis/list.verified.c0: 207.3-207.44",
  [783] = "src/test/resources/runtime-analysis/list.verified.c0: 208.30-208.39",
  [790] = "src/test/resources/runtime-analysis/list.verified.c0: 211.5-211.11",
  [791] = "src/test/resources/runtime-analysis/list.verified.c0: 211.14-211.43",
  [792] = "src/test/resources/runtime-analysis/list.verified.c0: 211.5-211.43",
  [794] = "src/test/resources/runtime-analysis/list.verified.c0: 212.5-212.11",
  [795] = "src/test/resources/runtime-analysis/list.verified.c0: 212.5-212.17",
  [797] = "src/test/resources/runtime-analysis/list.verified.c0: 213.5-213.12",
  [798] = "src/test/resources/runtime-analysis/list.verified.c0: 213.5-213.19",
  [804] = "src/test/resources/runtime-analysis/list.verified.c0: 219.12-219.22",
  [806] = "src/test/resources/runtime-analysis/list.verified.c0: 219.34-219.44",
  [807] = "src/test/resources/runtime-analysis/list.verified.c0: 219.34-219.49",
  [817] = "src/test/resources/runtime-analysis/list.verified.c0: 222.14-222.24",
  [825] = "src/test/resources/runtime-analysis/list.verified.c0: 231.5-231.13",
  [826] = "src/test/resources/runtime-analysis/list.verified.c0: 231.16-231.45",
  [827] = "src/test/resources/runtime-analysis/list.verified.c0: 231.5-231.45",
  [829] = "src/test/resources/runtime-analysis/list.verified.c0: 232.5-232.13",
  [830] = "src/test/resources/runtime-analysis/list.verified.c0: 232.5-232.19",
  [832] = "src/test/resources/runtime-analysis/list.verified.c0: 233.5-233.14",
  [833] = "src/test/resources/runtime-analysis/list.verified.c0: 233.17-233.27",
  [834] = "src/test/resources/runtime-analysis/list.verified.c0: 233.5-233.27",
  [836] = "src/test/resources/runtime-analysis/list.verified.c0: 234.5-234.15",
  [837] = "src/test/resources/runtime-analysis/list.verified.c0: 234.5-234.21",
  [853] = "src/test/resources/runtime-analysis/list.verified.c0: 254.18-254.51",
  [856] = "src/test/resources/runtime-analysis/list.verified.c0: 256.7-256.39",
  [858] = "src/test/resources/runtime-analysis/list.verified.c0: 257.3-257.30",
  [861] = "src/test/resources/runtime-analysis/list.verified.c0: 261.10-261.41",
  [875] = "src/test/resources/runtime-analysis/list.verified.c0: 274.7-274.20",
  [877] = "src/test/resources/runtime-analysis/list.verified.c0: 278.7-278.30",
  [882] = "src/test/resources/runtime-analysis/list.verified.c0: 283.45-283.55",
  [887] = "src/test/resources/runtime-analysis/list.verified.c0: 283.5-283.121",
  [890] = "src/test/resources/runtime-analysis/list.verified.c0: 284.45-284.55",
  [895] = "src/test/resources/runtime-analysis/list.verified.c0: 284.5-284.122",
  [896] = "src/test/resources/runtime-analysis/list.verified.c0: 285.12-285.22",
  [897] = "src/test/resources/runtime-analysis/list.verified.c0: 285.5-285.32",
  [898] = "src/test/resources/runtime-analysis/list.verified.c0: 286.21-286.32",
  [899] = "src/test/resources/runtime-analysis/list.verified.c0: 286.39-286.49",
  [900] = "src/test/resources/runtime-analysis/list.verified.c0: 286.5-286.72"
};
