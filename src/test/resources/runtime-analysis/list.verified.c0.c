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
void _c0_remove_sortedSegHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_prev, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sep_sortedSeg(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sep_sortedSegHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_prev, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields);
struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sortedSeg(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields);
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
        cc0_assert((_c0t__tmp_260 >= _c0v_aPrev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 104.9-104.33: assert failed"));
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
        cc0_assert((_c0v_cVal == _c0v_cVal), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 131.9-131.30: assert failed"));
        int _c0t__tmp_395 = (cc0_deref(struct _c0_Node, _c0v_c))._c0_val;
        cc0_assert((_c0t__tmp_395 >= _c0v_cPrev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 132.9-132.33: assert failed"));
      }
      if (((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && !((_c0v_c == NULL))) && !((_c0v_b == _c0v_c))) || (((((((((((!(_c0v__cond_1) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && _c0v__cond_2) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !((_c0v_b == _c0v_c))) && (_c0v_c == NULL)) && !((_c0v_b == _c0v_c))))) {
        cc0_assert((_c0v_bVal == _c0v_bVal), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 136.9-136.30: assert failed"));
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
        cc0_assert((_c0t__tmp_598 >= _c0v_aPrev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 161.9-161.33: assert failed"));
        struct _c0_Node* _c0t__tmp_599 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_next;
        int _c0t__tmp_600 = (cc0_deref(struct _c0_Node, _c0v_a))._c0_val;
        _c0_sortedSegHelper(_c0t__tmp_599, _c0v_c, _c0t__tmp_600, _c0v_cVal, _c0v__ownedFields);
      }
      if (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_2)) && !(_c0v__cond_1)) && !(_c0v__cond_1)) && !(_c0v__cond_3)) && !(_c0v__cond_6)) && !(_c0v__cond_7)) && !(_c0v__cond_8)) && !(_c0v__cond_7)) && !((_c0v_c == NULL))) && (_c0v_a == _c0v_c)) && !((_c0v_a == NULL)))) {
        cc0_assert((_c0v_cVal >= _c0v_aPrev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 166.9-166.31: assert failed"));
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
    cc0_assert((_c0v_cVal == _c0v_cVal), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 180.5-180.26: assert failed"));
    int _c0t__tmp_727 = (cc0_deref(struct _c0_Node, _c0v_c))._c0_val;
    cc0_assert((_c0t__tmp_727 >= _c0v_cPrev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 181.5-181.29: assert failed"));
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
  bool _c0v__cond_12 = false;
  bool _c0v__cond_13 = false;
  bool _c0v__cond_14 = false;
  bool _c0v__cond_15 = false;
  bool _c0v__cond_16 = false;
  bool _c0v__cond_17 = false;
  struct _c0_OwnedFields* _c0v__tempFields = NULL;
  struct _c0_Node* _c0v__ = NULL;
  _c0_add_sorted(_c0v_list, _c0v__ownedFields);
  _c0v__cond_1 = (_c0v_list == NULL);
  bool _c0t__tmp_741;
  if (((_c0v_list == NULL) || !((_c0v_list == NULL)))) {
    bool _c0t__tmp_740;
    if ((_c0v_list == NULL)) {
      _c0t__tmp_740 = true;
    } else {
      int _c0t__tmp_739 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_val;
      _c0t__tmp_740 = (_c0v_val <= _c0t__tmp_739);
    }
    _c0t__tmp_741 = _c0t__tmp_740;
  } else {
    _c0t__tmp_741 = false;
  }
  _c0v__cond_2 = _c0t__tmp_741;
  bool _c0t__tmp_743;
  if ((_c0v_list == NULL)) {
    _c0t__tmp_743 = true;
  } else {
    int _c0t__tmp_742 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_val;
    _c0t__tmp_743 = (_c0v_val <= _c0t__tmp_742);
  }
  if (_c0t__tmp_743) {
    struct _c0_Node* _c0t__tmp_744 = cc0_alloc(struct _c0_Node);
    _c0v_n = _c0t__tmp_744;
    int* _c0t__tmp_745;
    _c0t__tmp_745 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0__id);
    int _c0t__tmp_746 = _c0_addStructAcc(_c0v__ownedFields, 3);
    cc0_deref(int, _c0t__tmp_745) = _c0t__tmp_746;
    int* _c0t__tmp_747;
    _c0t__tmp_747 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_val);
    cc0_deref(int, _c0t__tmp_747) = _c0v_val;
    struct _c0_Node** _c0t__tmp_748;
    _c0t__tmp_748 = &((cc0_deref(struct _c0_Node, _c0v_n))._c0_next);
    cc0_deref(struct _c0_Node*, _c0t__tmp_748) = _c0v_list;
    return _c0v_n;
  } else {
    _c0v_curr = _c0v_list;
    bool _c0t__tmp_750;
    if (!((_c0v_list == NULL))) {
      struct _c0_Node* _c0t__tmp_749 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_next;
      _c0t__tmp_750 = (_c0t__tmp_749 == NULL);
    } else {
      _c0t__tmp_750 = false;
    }
    _c0v__cond_3 = _c0t__tmp_750;
    _c0v__cond_14 = true;
    _c0v__cond_4 = true;
    bool _c0t__tmp_752;
    if (!((_c0v_list == NULL))) {
      struct _c0_Node* _c0t__tmp_751 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_next;
      _c0t__tmp_752 = (_c0t__tmp_751 == NULL);
    } else {
      _c0t__tmp_752 = false;
    }
    _c0v__cond_5 = _c0t__tmp_752;
    bool _c0t__tmp_760;
    bool _c0t__tmp_758;
    bool _c0t__tmp_754;
    if (!((_c0v_curr == NULL))) {
      struct _c0_Node* _c0t__tmp_753 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      _c0t__tmp_754 = !((_c0t__tmp_753 == NULL));
    } else {
      _c0t__tmp_754 = false;
    }
    if ((_c0t__tmp_754 && !((_c0v_curr == NULL)))) {
      struct _c0_Node* _c0t__tmp_756 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      int _c0t__tmp_757 = (cc0_deref(struct _c0_Node, _c0t__tmp_756))._c0_val;
      _c0t__tmp_758 = (_c0t__tmp_757 < _c0v_val);
    } else {
      _c0t__tmp_758 = false;
    }
    if (_c0t__tmp_758) {
      struct _c0_Node* _c0t__tmp_759 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      _c0t__tmp_760 = !((_c0t__tmp_759 == NULL));
    } else {
      _c0t__tmp_760 = false;
    }
    _c0v__cond_6 = _c0t__tmp_760;
    while (true) {
      bool _c0t__tmp_764;
      struct _c0_Node* _c0t__tmp_761 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      if ((_c0t__tmp_761 != NULL)) {
        struct _c0_Node* _c0t__tmp_762 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        int _c0t__tmp_763 = (cc0_deref(struct _c0_Node, _c0t__tmp_762))._c0_val;
        _c0t__tmp_764 = (_c0t__tmp_763 < _c0v_val);
      } else {
        _c0t__tmp_764 = false;
      }
      if (_c0t__tmp_764) {
      } else {
        break;
      }
      _c0v_prev = _c0v_curr;
      struct _c0_Node* _c0t__tmp_765 = (cc0_deref(struct _c0_Node, _c0v_prev))._c0_next;
      _c0v_curr = _c0t__tmp_765;
      _c0v__cond_7 = (_c0v_list == _c0v_prev);
      _c0v__cond_8 = (_c0v_curr == _c0v_curr);
      _c0v__cond_9 = (_c0v_curr == NULL);
      _c0v__cond_10 = (_c0v_list == _c0v_prev);
      if ((_c0v_list == _c0v_prev)) {
      } else {
        _c0v__cond_11 = (_c0v_prev == _c0v_curr);
        _c0v__cond_12 = (_c0v_curr == NULL);
        struct _c0_Node* _c0t__tmp_766 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_next;
        int _c0t__tmp_767 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_val;
        int _c0t__tmp_768 = (cc0_deref(struct _c0_Node, _c0v_prev))._c0_val;
        int _c0t__tmp_769 = (cc0_deref(struct _c0_Node, _c0v_prev))._c0_val;
        int _c0t__tmp_770 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_val;
        _c0_appendLemmaLoopBody(_c0t__tmp_766, _c0v_prev, _c0v_curr, _c0t__tmp_767, _c0t__tmp_768, _c0t__tmp_769, _c0t__tmp_770, _c0v__ownedFields);
        _c0v__cond_13 = (_c0v_curr == NULL);
      }
      if ((((((((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !((_c0v_list == _c0v_curr))) || ((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !((_c0v_list == _c0v_curr)))) || ((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !((_c0v_list == _c0v_curr)))) || ((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !((_c0v_list == _c0v_curr)))) || (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !((_c0v_list == _c0v_curr)))) || (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !((_c0v_list == _c0v_curr)))) || (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !((_c0v_list == _c0v_curr)))) || (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !((_c0v_list == _c0v_curr))))) {
        int _c0t__tmp_895;
        if ((_c0v_list != NULL)) {
          int _c0t__tmp_894 = (cc0_deref(struct _c0_Node, _c0v_list))._c0__id;
          _c0t__tmp_895 = _c0t__tmp_894;
        } else {
          _c0t__tmp_895 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_895, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
        int _c0t__tmp_897;
        if ((_c0v_list != NULL)) {
          int _c0t__tmp_896 = (cc0_deref(struct _c0_Node, _c0v_list))._c0__id;
          _c0t__tmp_897 = _c0t__tmp_896;
        } else {
          _c0t__tmp_897 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_897, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
      }
      if ((((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !((_c0v_list == _c0v_curr))) || ((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !((_c0v_list == _c0v_curr)))) || (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !((_c0v_list == _c0v_curr)))) || (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !((_c0v_list == _c0v_curr))))) {
        struct _c0_Node* _c0t__tmp_959 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_next;
        int _c0t__tmp_960 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_val;
        int _c0t__tmp_961 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_val;
        _c0_sortedSegHelper(_c0t__tmp_959, _c0v_curr, _c0t__tmp_960, _c0t__tmp_961, _c0v__ownedFields);
      }
      _c0v__cond_15 = (_c0v_list == _c0v_curr);
      if ((((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) || ((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15))) || (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15))) || (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)))) {
        int _c0t__tmp_1024;
        if ((_c0v_curr != NULL)) {
          int _c0t__tmp_1023 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
          _c0t__tmp_1024 = _c0t__tmp_1023;
        } else {
          _c0t__tmp_1024 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1024, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
        int _c0t__tmp_1026;
        if ((_c0v_curr != NULL)) {
          int _c0t__tmp_1025 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
          _c0t__tmp_1026 = _c0t__tmp_1025;
        } else {
          _c0t__tmp_1026 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1026, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
      }
      bool _c0t__tmp_1028;
      if (!((_c0v_curr == NULL))) {
        struct _c0_Node* _c0t__tmp_1027 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        _c0t__tmp_1028 = (_c0t__tmp_1027 == NULL);
      } else {
        _c0t__tmp_1028 = false;
      }
      _c0v__cond_16 = _c0t__tmp_1028;
      _c0v__cond_17 = true;
      int* _c0t__tmp_1029 = (cc0_deref(struct _c0_OwnedFields, _c0v__ownedFields))._c0_instanceCounter;
      struct _c0_OwnedFields* _c0t__tmp_1030 = _c0_initOwnedFields(_c0t__tmp_1029);
      _c0v__tempFields = _c0t__tmp_1030;
      bool _c0t__tmp_1103;
      bool _c0t__tmp_1084;
      bool _c0t__tmp_1065;
      bool _c0t__tmp_1047;
      if ((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && !(_c0v__cond_16))) {
        struct _c0_Node* _c0t__tmp_1046 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        _c0t__tmp_1047 = !((_c0t__tmp_1046 == NULL));
      } else {
        _c0t__tmp_1047 = false;
      }
      if (_c0t__tmp_1047) {
        _c0t__tmp_1065 = true;
      } else {
        bool _c0t__tmp_1064;
        if ((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && !(_c0v__cond_16))) {
          struct _c0_Node* _c0t__tmp_1063 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_1064 = !((_c0t__tmp_1063 == NULL));
        } else {
          _c0t__tmp_1064 = false;
        }
        _c0t__tmp_1065 = _c0t__tmp_1064;
      }
      if (_c0t__tmp_1065) {
        _c0t__tmp_1084 = true;
      } else {
        bool _c0t__tmp_1083;
        if (((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && !(_c0v__cond_16))) {
          struct _c0_Node* _c0t__tmp_1082 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_1083 = !((_c0t__tmp_1082 == NULL));
        } else {
          _c0t__tmp_1083 = false;
        }
        _c0t__tmp_1084 = _c0t__tmp_1083;
      }
      if (_c0t__tmp_1084) {
        _c0t__tmp_1103 = true;
      } else {
        bool _c0t__tmp_1102;
        if (((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && !(_c0v__cond_16))) {
          struct _c0_Node* _c0t__tmp_1101 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_1102 = !((_c0t__tmp_1101 == NULL));
        } else {
          _c0t__tmp_1102 = false;
        }
        _c0t__tmp_1103 = _c0t__tmp_1102;
      }
      if (_c0t__tmp_1103) {
        int _c0t__tmp_1107;
        struct _c0_Node* _c0t__tmp_1104 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        if ((_c0t__tmp_1104 != NULL)) {
          struct _c0_Node* _c0t__tmp_1105 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          int _c0t__tmp_1106 = (cc0_deref(struct _c0_Node, _c0t__tmp_1105))._c0__id;
          _c0t__tmp_1107 = _c0t__tmp_1106;
        } else {
          _c0t__tmp_1107 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1107, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
        int _c0t__tmp_1111;
        struct _c0_Node* _c0t__tmp_1108 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        if ((_c0t__tmp_1108 != NULL)) {
          struct _c0_Node* _c0t__tmp_1109 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          int _c0t__tmp_1110 = (cc0_deref(struct _c0_Node, _c0t__tmp_1109))._c0__id;
          _c0t__tmp_1111 = _c0t__tmp_1110;
        } else {
          _c0t__tmp_1111 = -(1);
        }
        _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1111, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
      }
      if (((((((((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && !(_c0v__cond_16)) || ((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && _c0v__cond_16) && _c0v__cond_17)) || (((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && !(_c0v__cond_16))) || ((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && _c0v__cond_16) && _c0v__cond_17)) || ((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && !(_c0v__cond_16))) || (((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && _c0v__cond_16) && _c0v__cond_17)) || ((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && !(_c0v__cond_16))) || (((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && _c0v__cond_16) && _c0v__cond_17))) {
        int _c0t__tmp_1247 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_val;
        cc0_assert((_c0t__tmp_1247 <= _c0v_val), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 288.9-288.34: assert failed"));
        int _c0t__tmp_1248 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_val;
        _c0_sortedSeg(_c0v_list, _c0v_curr, _c0t__tmp_1248, _c0v__ownedFields);
      }
      bool _c0t__tmp_1321;
      bool _c0t__tmp_1302;
      bool _c0t__tmp_1283;
      bool _c0t__tmp_1265;
      if ((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && !(_c0v__cond_16))) {
        struct _c0_Node* _c0t__tmp_1264 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        _c0t__tmp_1265 = !((_c0t__tmp_1264 == NULL));
      } else {
        _c0t__tmp_1265 = false;
      }
      if (_c0t__tmp_1265) {
        _c0t__tmp_1283 = true;
      } else {
        bool _c0t__tmp_1282;
        if ((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && !(_c0v__cond_3)) && _c0v__cond_4) && !(_c0v__cond_5)) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && !(_c0v__cond_16))) {
          struct _c0_Node* _c0t__tmp_1281 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_1282 = !((_c0t__tmp_1281 == NULL));
        } else {
          _c0t__tmp_1282 = false;
        }
        _c0t__tmp_1283 = _c0t__tmp_1282;
      }
      if (_c0t__tmp_1283) {
        _c0t__tmp_1302 = true;
      } else {
        bool _c0t__tmp_1301;
        if (((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && !(_c0v__cond_16))) {
          struct _c0_Node* _c0t__tmp_1300 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_1301 = !((_c0t__tmp_1300 == NULL));
        } else {
          _c0t__tmp_1301 = false;
        }
        _c0t__tmp_1302 = _c0t__tmp_1301;
      }
      if (_c0t__tmp_1302) {
        _c0t__tmp_1321 = true;
      } else {
        bool _c0t__tmp_1320;
        if (((((((((((((((((!(_c0v__cond_1) && !(_c0v__cond_2)) && _c0v__cond_3) && _c0v__cond_14) && _c0v__cond_4) && _c0v__cond_5) && _c0v__cond_6) && !(_c0v__cond_7)) && _c0v__cond_8) && !(_c0v__cond_9)) && !(_c0v__cond_10)) && !(_c0v__cond_11)) && !(_c0v__cond_12)) && !(_c0v__cond_11)) && !(_c0v__cond_13)) && !(_c0v__cond_15)) && !(_c0v__cond_16))) {
          struct _c0_Node* _c0t__tmp_1319 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          _c0t__tmp_1320 = !((_c0t__tmp_1319 == NULL));
        } else {
          _c0t__tmp_1320 = false;
        }
        _c0t__tmp_1321 = _c0t__tmp_1320;
      }
      if (_c0t__tmp_1321) {
        struct _c0_Node* _c0t__tmp_1322 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        struct _c0_Node* _c0t__tmp_1323 = (cc0_deref(struct _c0_Node, _c0t__tmp_1322))._c0_next;
        struct _c0_Node* _c0t__tmp_1324 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        int _c0t__tmp_1325 = (cc0_deref(struct _c0_Node, _c0t__tmp_1324))._c0_val;
        _c0_sortedSegHelper(_c0t__tmp_1323, NULL, _c0t__tmp_1325, -(1), _c0v__ownedFields);
      }
      int _c0t__tmp_1327;
      if ((_c0v_curr != NULL)) {
        int _c0t__tmp_1326 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
        _c0t__tmp_1327 = _c0t__tmp_1326;
      } else {
        _c0t__tmp_1327 = -(1);
      }
      _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_1327, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
      int _c0t__tmp_1329;
      if ((_c0v_curr != NULL)) {
        int _c0t__tmp_1328 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
        _c0t__tmp_1329 = _c0t__tmp_1328;
      } else {
        _c0t__tmp_1329 = -(1);
      }
      _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_1329, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
      int _c0t__tmp_1330 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_val;
      _c0_sep_sortedSeg(_c0v_list, _c0v_curr, _c0t__tmp_1330, _c0v__tempFields);
      struct _c0_Node* _c0t__tmp_1331 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
      if (!((_c0t__tmp_1331 == NULL))) {
        int _c0t__tmp_1335;
        struct _c0_Node* _c0t__tmp_1332 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        if ((_c0t__tmp_1332 != NULL)) {
          struct _c0_Node* _c0t__tmp_1333 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          int _c0t__tmp_1334 = (cc0_deref(struct _c0_Node, _c0t__tmp_1333))._c0__id;
          _c0t__tmp_1335 = _c0t__tmp_1334;
        } else {
          _c0t__tmp_1335 = -(1);
        }
        _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_1335, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
        int _c0t__tmp_1339;
        struct _c0_Node* _c0t__tmp_1336 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        if ((_c0t__tmp_1336 != NULL)) {
          struct _c0_Node* _c0t__tmp_1337 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
          int _c0t__tmp_1338 = (cc0_deref(struct _c0_Node, _c0t__tmp_1337))._c0__id;
          _c0t__tmp_1339 = _c0t__tmp_1338;
        } else {
          _c0t__tmp_1339 = -(1);
        }
        _c0_addAccEnsureSeparate(_c0v__tempFields, _c0t__tmp_1339, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
        struct _c0_Node* _c0t__tmp_1340 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        struct _c0_Node* _c0t__tmp_1341 = (cc0_deref(struct _c0_Node, _c0t__tmp_1340))._c0_next;
        struct _c0_Node* _c0t__tmp_1342 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        int _c0t__tmp_1343 = (cc0_deref(struct _c0_Node, _c0t__tmp_1342))._c0_val;
        _c0_sep_sortedSegHelper(_c0t__tmp_1341, NULL, _c0t__tmp_1343, -(1), _c0v__tempFields);
      }
    }
    struct _c0_Node* _c0t__tmp_1344 = cc0_alloc(struct _c0_Node);
    _c0v_tmp = _c0t__tmp_1344;
    int* _c0t__tmp_1345;
    _c0t__tmp_1345 = &((cc0_deref(struct _c0_Node, _c0v_tmp))._c0__id);
    int _c0t__tmp_1346 = _c0_addStructAcc(_c0v__ownedFields, 3);
    cc0_deref(int, _c0t__tmp_1345) = _c0t__tmp_1346;
    int* _c0t__tmp_1347;
    _c0t__tmp_1347 = &((cc0_deref(struct _c0_Node, _c0v_tmp))._c0_val);
    cc0_deref(int, _c0t__tmp_1347) = _c0v_val;
    struct _c0_Node** _c0t__tmp_1348;
    _c0t__tmp_1348 = &((cc0_deref(struct _c0_Node, _c0v_tmp))._c0_next);
    struct _c0_Node* _c0t__tmp_1349 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
    cc0_deref(struct _c0_Node*, _c0t__tmp_1348) = _c0t__tmp_1349;
    struct _c0_Node** _c0t__tmp_1350;
    _c0t__tmp_1350 = &((cc0_deref(struct _c0_Node, _c0v_curr))._c0_next);
    cc0_deref(struct _c0_Node*, _c0t__tmp_1350) = _c0v_tmp;
    if ((_c0v_list == _c0v_curr)) {
    } else {
      struct _c0_Node* _c0t__tmp_1351 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_next;
      int _c0t__tmp_1352 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_val;
      int _c0t__tmp_1353 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_val;
      _c0_remove_sortedSegHelper(_c0t__tmp_1351, _c0v_curr, _c0t__tmp_1352, _c0t__tmp_1353, _c0v__ownedFields);
      if (!((_c0v__ == NULL))) {
        int _c0t__tmp_1354 = (cc0_deref(struct _c0_Node, _c0v__))._c0__id;
        _c0_loseAcc(_c0v__ownedFields, _c0t__tmp_1354, 0);
        int _c0t__tmp_1355 = (cc0_deref(struct _c0_Node, _c0v__))._c0__id;
        _c0_loseAcc(_c0v__ownedFields, _c0t__tmp_1355, 1);
      }
      if (!((_c0v_curr == _c0v__))) {
        int _c0t__tmp_1356 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
        _c0_loseAcc(_c0v__ownedFields, _c0t__tmp_1356, 0);
        int _c0t__tmp_1357 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0__id;
        _c0_loseAcc(_c0v__ownedFields, _c0t__tmp_1357, 1);
        struct _c0_Node* _c0t__tmp_1358 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_next;
        int _c0t__tmp_1359 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_val;
        _c0_remove_sortedSegHelper(_c0t__tmp_1358, _c0v__, _c0t__tmp_1359, -(1), _c0v__ownedFields);
      }
      struct _c0_Node* _c0t__tmp_1360 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_next;
      int _c0t__tmp_1361 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_val;
      int _c0t__tmp_1362 = (cc0_deref(struct _c0_Node, _c0v_curr))._c0_val;
      int* _c0t__tmp_1363 = (cc0_deref(struct _c0_OwnedFields, _c0v__ownedFields))._c0_instanceCounter;
      _c0_appendLemmaAfterLoopBody(_c0t__tmp_1360, _c0v_curr, NULL, _c0t__tmp_1361, _c0t__tmp_1362, -(1), _c0t__tmp_1363);
      struct _c0_Node* _c0t__tmp_1364 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_next;
      int _c0t__tmp_1365 = (cc0_deref(struct _c0_Node, _c0v_list))._c0_val;
      _c0_add_sortedSegHelper(_c0t__tmp_1364, _c0v__, _c0t__tmp_1365, -(1), _c0v__ownedFields);
      if (!((_c0v__ == NULL))) {
        int _c0t__tmp_1366 = (cc0_deref(struct _c0_Node, _c0v__))._c0__id;
        _c0_addAcc(_c0v__ownedFields, _c0t__tmp_1366, 3, 0);
        int _c0t__tmp_1367 = (cc0_deref(struct _c0_Node, _c0v__))._c0__id;
        _c0_addAcc(_c0v__ownedFields, _c0t__tmp_1367, 3, 1);
      }
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
  struct _c0_OwnedFields* _c0v__tempFields = NULL;
  int* _c0t__tmp_1368 = cc0_alloc(int);
  _c0v__instanceCounter = _c0t__tmp_1368;
  _c0v_stress = 0;
  struct _c0_Node* _c0t__tmp_1369 = _c0_create_list(3, _c0v__instanceCounter);
  _c0v_l = _c0t__tmp_1369;
  _c0v_i = 0;
  while ((_c0v_i < _c0v_stress)) {
    struct _c0_OwnedFields* _c0t__tmp_1370 = _c0_initOwnedFields(_c0v__instanceCounter);
    _c0v__tempFields = _c0t__tmp_1370;
    struct _c0_Node* _c0t__tmp_1371 = _c0_list_insert(_c0v_l, 1, _c0v__tempFields);
    _c0v_l1 = _c0t__tmp_1371;
    _c0v_i = (_c0v_i + 1);
    _c0v_l = _c0v_l1;
  }
  return 0;
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_remove_sortedSegHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_prev, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields) {
  if (!((_c0v_start == _c0v_end))) {
    int _c0t__tmp_1372 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_loseAcc(_c0v__ownedFields, _c0t__tmp_1372, 0);
    int _c0t__tmp_1373 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
    _c0_loseAcc(_c0v__ownedFields, _c0t__tmp_1373, 1);
    struct _c0_Node* _c0t__tmp_1374 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    int _c0t__tmp_1375 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_val;
    _c0_remove_sortedSegHelper(_c0t__tmp_1374, _c0v_end, _c0t__tmp_1375, _c0v_endVal, _c0v__ownedFields);
  }
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sep_sortedSeg(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields) {
  if (!((_c0v_start == _c0v_end))) {
    int _c0t__tmp_1377;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_1376 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_1377 = _c0t__tmp_1376;
    } else {
      _c0t__tmp_1377 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__ownedFields, _c0t__tmp_1377, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
    int _c0t__tmp_1379;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_1378 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_1379 = _c0t__tmp_1378;
    } else {
      _c0t__tmp_1379 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__ownedFields, _c0t__tmp_1379, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
    struct _c0_Node* _c0t__tmp_1380 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    int _c0t__tmp_1381 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_val;
    _c0_sep_sortedSegHelper(_c0t__tmp_1380, _c0v_end, _c0t__tmp_1381, _c0v_endVal, _c0v__ownedFields);
  }
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sep_sortedSegHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_prev, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields) {
  if (!((_c0v_start == _c0v_end))) {
    int _c0t__tmp_1383;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_1382 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_1383 = _c0t__tmp_1382;
    } else {
      _c0t__tmp_1383 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__ownedFields, _c0t__tmp_1383, 0, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.val"));
    int _c0t__tmp_1385;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_1384 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_1385 = _c0t__tmp_1384;
    } else {
      _c0t__tmp_1385 = -(1);
    }
    _c0_addAccEnsureSeparate(_c0v__ownedFields, _c0t__tmp_1385, 1, 3, c0_string_fromliteral("Overlapping field permissions for struct Node.next"));
    struct _c0_Node* _c0t__tmp_1386 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    int _c0t__tmp_1387 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_val;
    _c0_sep_sortedSegHelper(_c0t__tmp_1386, _c0v_end, _c0t__tmp_1387, _c0v_endVal, _c0v__ownedFields);
  }
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sortedSeg(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields) {
  if ((_c0v_start == _c0v_end)) {
    cc0_assert(true, c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 395.5-395.18: assert failed"));
  } else {
    int _c0t__tmp_1389;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_1388 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_1389 = _c0t__tmp_1388;
    } else {
      _c0t__tmp_1389 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1389, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
    int _c0t__tmp_1391;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_1390 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_1391 = _c0t__tmp_1390;
    } else {
      _c0t__tmp_1391 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1391, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
    struct _c0_Node* _c0t__tmp_1392 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    int _c0t__tmp_1393 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_val;
    _c0_sortedSegHelper(_c0t__tmp_1392, _c0v_end, _c0t__tmp_1393, _c0v_endVal, _c0v__ownedFields);
  }
}

struct _c0_Node;
struct _c0_Node;
struct _c0_OwnedFields;
void _c0_sortedSegHelper(struct _c0_Node* _c0v_start, struct _c0_Node* _c0v_end, int _c0v_prev, int _c0v_endVal, struct _c0_OwnedFields* _c0v__ownedFields) {
  if ((_c0v_start == _c0v_end)) {
    if ((_c0v_end == NULL)) {
      cc0_assert(true, c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 411.7-411.20: assert failed"));
    } else {
      cc0_assert((_c0v_endVal >= _c0v_prev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 415.7-415.30: assert failed"));
    }
  } else {
    int _c0t__tmp_1395;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_1394 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_1395 = _c0t__tmp_1394;
    } else {
      _c0t__tmp_1395 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1395, 0, c0_string_fromliteral("Field access runtime check failed for struct Node.val"));
    int _c0t__tmp_1397;
    if ((_c0v_start != NULL)) {
      int _c0t__tmp_1396 = (cc0_deref(struct _c0_Node, _c0v_start))._c0__id;
      _c0t__tmp_1397 = _c0t__tmp_1396;
    } else {
      _c0t__tmp_1397 = -(1);
    }
    _c0_assertAcc(_c0v__ownedFields, _c0t__tmp_1397, 1, c0_string_fromliteral("Field access runtime check failed for struct Node.next"));
    int _c0t__tmp_1398 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_val;
    cc0_assert((_c0t__tmp_1398 >= _c0v_prev), c0_string_fromliteral("src/test/resources/runtime-analysis/list.verified.c0: 422.5-422.32: assert failed"));
    struct _c0_Node* _c0t__tmp_1399 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_next;
    int _c0t__tmp_1400 = (cc0_deref(struct _c0_Node, _c0v_start))._c0_val;
    _c0_sortedSegHelper(_c0t__tmp_1399, _c0v_end, _c0t__tmp_1400, _c0v_endVal, _c0v__ownedFields);
  }
}
long map_length = 1351;
const char* source_map[1351] = {
  [67] = "/workspaces/gvc0/src/main/resources/runtime.c0: 15.12-15.31",
  [75] = "/workspaces/gvc0/src/main/resources/runtime.c0: 20.3-20.26",
  [76] = "/workspaces/gvc0/src/main/resources/runtime.c0: 20.3-20.44",
  [79] = "/workspaces/gvc0/src/main/resources/runtime.c0: 22.3-22.19",
  [80] = "/workspaces/gvc0/src/main/resources/runtime.c0: 22.22-22.48",
  [81] = "/workspaces/gvc0/src/main/resources/runtime.c0: 22.3-22.48",
  [83] = "/workspaces/gvc0/src/main/resources/runtime.c0: 23.3-23.19",
  [84] = "/workspaces/gvc0/src/main/resources/runtime.c0: 23.47-23.63",
  [86] = "/workspaces/gvc0/src/main/resources/runtime.c0: 23.3-23.64",
  [90] = "/workspaces/gvc0/src/main/resources/runtime.c0: 25.22-25.38",
  [96] = "/workspaces/gvc0/src/main/resources/runtime.c0: 26.5-26.21",
  [98] = "/workspaces/gvc0/src/main/resources/runtime.c0: 26.5-26.24",
  [99] = "/workspaces/gvc0/src/main/resources/runtime.c0: 26.5-26.31",
  [108] = "/workspaces/gvc0/src/main/resources/runtime.c0: 34.21-34.37",
  [111] = "/workspaces/gvc0/src/main/resources/runtime.c0: 35.3-35.19",
  [112] = "/workspaces/gvc0/src/main/resources/runtime.c0: 35.22-35.48",
  [113] = "/workspaces/gvc0/src/main/resources/runtime.c0: 35.3-35.48",
  [114] = "/workspaces/gvc0/src/main/resources/runtime.c0: 36.56-36.72",
  [122] = "/workspaces/gvc0/src/main/resources/runtime.c0: 38.8-38.24",
  [123] = "/workspaces/gvc0/src/main/resources/runtime.c0: 38.8-38.27",
  [125] = "/workspaces/gvc0/src/main/resources/runtime.c0: 38.40-38.56",
  [126] = "/workspaces/gvc0/src/main/resources/runtime.c0: 38.40-38.59",
  [127] = "/workspaces/gvc0/src/main/resources/runtime.c0: 38.40-38.68",
  [133] = "/workspaces/gvc0/src/main/resources/runtime.c0: 39.19-39.35",
  [134] = "/workspaces/gvc0/src/main/resources/runtime.c0: 39.19-39.38",
  [135] = "/workspaces/gvc0/src/main/resources/runtime.c0: 39.19-39.43",
  [137] = "/workspaces/gvc0/src/main/resources/runtime.c0: 40.34-40.50",
  [138] = "/workspaces/gvc0/src/main/resources/runtime.c0: 40.24-40.51",
  [141] = "/workspaces/gvc0/src/main/resources/runtime.c0: 41.15-41.36",
  [146] = "/workspaces/gvc0/src/main/resources/runtime.c0: 42.41-42.57",
  [147] = "/workspaces/gvc0/src/main/resources/runtime.c0: 42.24-42.57",
  [151] = "/workspaces/gvc0/src/main/resources/runtime.c0: 44.9-44.30",
  [152] = "/workspaces/gvc0/src/main/resources/runtime.c0: 44.33-44.49",
  [153] = "/workspaces/gvc0/src/main/resources/runtime.c0: 44.33-44.52",
  [154] = "/workspaces/gvc0/src/main/resources/runtime.c0: 44.9-44.52",
  [161] = "/workspaces/gvc0/src/main/resources/runtime.c0: 47.3-47.19",
  [162] = "/workspaces/gvc0/src/main/resources/runtime.c0: 47.3-47.33",
  [167] = "/workspaces/gvc0/src/main/resources/runtime.c0: 52.27-52.43",
  [168] = "/workspaces/gvc0/src/main/resources/runtime.c0: 52.17-52.44",
  [171] = "/workspaces/gvc0/src/main/resources/runtime.c0: 53.11-53.27",
  [172] = "/workspaces/gvc0/src/main/resources/runtime.c0: 53.11-53.34",
  [178] = "/workspaces/gvc0/src/main/resources/runtime.c0: 54.13-54.29",
  [179] = "/workspaces/gvc0/src/main/resources/runtime.c0: 54.13-54.36",
  [180] = "/workspaces/gvc0/src/main/resources/runtime.c0: 54.13-54.45",
  [182] = "/workspaces/gvc0/src/main/resources/runtime.c0: 54.49-54.65",
  [183] = "/workspaces/gvc0/src/main/resources/runtime.c0: 54.49-54.72",
  [184] = "/workspaces/gvc0/src/main/resources/runtime.c0: 54.49-54.77",
  [190] = "/workspaces/gvc0/src/main/resources/runtime.c0: 55.20-55.36",
  [191] = "/workspaces/gvc0/src/main/resources/runtime.c0: 55.20-55.43",
  [194] = "/workspaces/gvc0/src/main/resources/runtime.c0: 57.35-57.51",
  [195] = "/workspaces/gvc0/src/main/resources/runtime.c0: 57.21-57.51",
  [204] = "/workspaces/gvc0/src/main/resources/runtime.c0: 68.6-68.20",
  [205] = "/workspaces/gvc0/src/main/resources/runtime.c0: 68.24-68.40",
  [207] = "/workspaces/gvc0/src/main/resources/runtime.c0: 68.51-68.63",
  [209] = "/workspaces/gvc0/src/main/resources/runtime.c0: 70.30-70.46",
  [210] = "/workspaces/gvc0/src/main/resources/runtime.c0: 70.20-70.47",
  [214] = "/workspaces/gvc0/src/main/resources/runtime.c0: 71.9-71.25",
  [215] = "/workspaces/gvc0/src/main/resources/runtime.c0: 71.9-71.37",
  [217] = "/workspaces/gvc0/src/main/resources/runtime.c0: 71.50-71.66",
  [218] = "/workspaces/gvc0/src/main/resources/runtime.c0: 71.50-71.78",
  [219] = "/workspaces/gvc0/src/main/resources/runtime.c0: 71.50-71.87",
  [228] = "/workspaces/gvc0/src/main/resources/runtime.c0: 71.121-71.137",
  [229] = "/workspaces/gvc0/src/main/resources/runtime.c0: 71.102-71.137",
  [234] = "/workspaces/gvc0/src/main/resources/runtime.c0: 74.3-74.19",
  [236] = "/workspaces/gvc0/src/main/resources/runtime.c0: 74.3-74.31",
  [237] = "/workspaces/gvc0/src/main/resources/runtime.c0: 74.3-74.39",
  [238] = "/workspaces/gvc0/src/main/resources/runtime.c0: 75.3-75.22",
  [240] = "/workspaces/gvc0/src/main/resources/runtime.c0: 77.3-77.18",
  [242] = "/workspaces/gvc0/src/main/resources/runtime.c0: 77.3-77.49",
  [244] = "/workspaces/gvc0/src/main/resources/runtime.c0: 78.3-78.16",
  [245] = "/workspaces/gvc0/src/main/resources/runtime.c0: 78.3-78.28",
  [247] = "/workspaces/gvc0/src/main/resources/runtime.c0: 79.3-79.13",
  [248] = "/workspaces/gvc0/src/main/resources/runtime.c0: 79.3-79.19",
  [250] = "/workspaces/gvc0/src/main/resources/runtime.c0: 80.3-80.17",
  [251] = "/workspaces/gvc0/src/main/resources/runtime.c0: 80.3-80.25",
  [255] = "/workspaces/gvc0/src/main/resources/runtime.c0: 82.20-82.33",
  [261] = "/workspaces/gvc0/src/main/resources/runtime.c0: 83.5-83.20",
  [263] = "/workspaces/gvc0/src/main/resources/runtime.c0: 83.5-83.23",
  [264] = "/workspaces/gvc0/src/main/resources/runtime.c0: 83.5-83.32",
  [271] = "/workspaces/gvc0/src/main/resources/runtime.c0: 86.5-86.25",
  [272] = "/workspaces/gvc0/src/main/resources/runtime.c0: 86.28-86.41",
  [273] = "/workspaces/gvc0/src/main/resources/runtime.c0: 86.5-86.41",
  [276] = "/workspaces/gvc0/src/main/resources/runtime.c0: 88.5-88.25",
  [277] = "/workspaces/gvc0/src/main/resources/runtime.c0: 88.5-88.29",
  [279] = "/workspaces/gvc0/src/main/resources/runtime.c0: 90.10-90.26",
  [280] = "/workspaces/gvc0/src/main/resources/runtime.c0: 90.10-90.38",
  [285] = "/workspaces/gvc0/src/main/resources/runtime.c0: 94.28-94.51",
  [286] = "/workspaces/gvc0/src/main/resources/runtime.c0: 94.27-94.51",
  [287] = "/workspaces/gvc0/src/main/resources/runtime.c0: 94.5-94.69",
  [288] = "/workspaces/gvc0/src/main/resources/runtime.c0: 95.7-95.30",
  [289] = "/workspaces/gvc0/src/main/resources/runtime.c0: 95.5-95.36",
  [290] = "/workspaces/gvc0/src/main/resources/runtime.c0: 96.14-96.37",
  [291] = "/workspaces/gvc0/src/main/resources/runtime.c0: 96.12-96.38",
  [296] = "/workspaces/gvc0/src/main/resources/runtime.c0: 100.24-100.41",
  [299] = "/workspaces/gvc0/src/main/resources/runtime.c0: 102.9-102.24",
  [300] = "/workspaces/gvc0/src/main/resources/runtime.c0: 102.9-102.36",
  [302] = "/workspaces/gvc0/src/main/resources/runtime.c0: 103.9-103.34",
  [303] = "/workspaces/gvc0/src/main/resources/runtime.c0: 104.9-104.24",
  [305] = "/workspaces/gvc0/src/main/resources/runtime.c0: 104.9-104.36",
  [306] = "/workspaces/gvc0/src/main/resources/runtime.c0: 104.9-104.43",
  [309] = "/workspaces/gvc0/src/main/resources/runtime.c0: 107.13-107.57",
  [311] = "/workspaces/gvc0/src/main/resources/runtime.c0: 108.5-108.20",
  [313] = "/workspaces/gvc0/src/main/resources/runtime.c0: 108.5-108.32",
  [314] = "/workspaces/gvc0/src/main/resources/runtime.c0: 108.5-108.39",
  [315] = "/workspaces/gvc0/src/main/resources/runtime.c0: 109.5-109.30",
  [320] = "/workspaces/gvc0/src/main/resources/runtime.c0: 114.27-114.44",
  [326] = "/workspaces/gvc0/src/main/resources/runtime.c0: 115.28-115.45",
  [327] = "/workspaces/gvc0/src/main/resources/runtime.c0: 115.28-115.57",
  [331] = "/workspaces/gvc0/src/main/resources/runtime.c0: 116.9-116.29",
  [337] = "/workspaces/gvc0/src/main/resources/runtime.c0: 121.27-121.44",
  [340] = "/workspaces/gvc0/src/main/resources/runtime.c0: 123.19-123.63",
  [343] = "/workspaces/gvc0/src/main/resources/runtime.c0: 124.16-124.33",
  [344] = "/workspaces/gvc0/src/main/resources/runtime.c0: 124.16-124.45",
  [346] = "/workspaces/gvc0/src/main/resources/runtime.c0: 125.9-125.29",
  [350] = "/workspaces/gvc0/src/main/resources/runtime.c0: 127.5-127.22",
  [352] = "/workspaces/gvc0/src/main/resources/runtime.c0: 127.5-127.34",
  [353] = "/workspaces/gvc0/src/main/resources/runtime.c0: 127.5-127.41",
  [354] = "/workspaces/gvc0/src/main/resources/runtime.c0: 128.5-128.32",
  [358] = "/workspaces/gvc0/src/main/resources/runtime.c0: 132.27-132.44",
  [361] = "/workspaces/gvc0/src/main/resources/runtime.c0: 134.26-134.40",
  [363] = "/workspaces/gvc0/src/main/resources/runtime.c0: 135.13-135.85",
  [366] = "/workspaces/gvc0/src/main/resources/runtime.c0: 136.18-136.34",
  [367] = "/workspaces/gvc0/src/main/resources/runtime.c0: 136.18-136.46",
  [369] = "/workspaces/gvc0/src/main/resources/runtime.c0: 137.13-137.29",
  [371] = "/workspaces/gvc0/src/main/resources/runtime.c0: 137.13-137.41",
  [372] = "/workspaces/gvc0/src/main/resources/runtime.c0: 137.13-137.49",
  [373] = "/workspaces/gvc0/src/main/resources/runtime.c0: 138.13-138.39",
  [376] = "/workspaces/gvc0/src/main/resources/runtime.c0: 140.12-140.33",
  [379] = "/workspaces/gvc0/src/main/resources/runtime.c0: 140.40-140.55",
  [380] = "/workspaces/gvc0/src/main/resources/runtime.c0: 140.40-140.62",
  [389] = "/workspaces/gvc0/src/main/resources/runtime.c0: 146.26-146.42",
  [395] = "/workspaces/gvc0/src/main/resources/runtime.c0: 147.38-147.54",
  [396] = "/workspaces/gvc0/src/main/resources/runtime.c0: 147.38-147.57",
  [401] = "/workspaces/gvc0/src/main/resources/runtime.c0: 149.35-149.53",
  [407] = "/workspaces/gvc0/src/main/resources/runtime.c0: 150.36-150.51",
  [408] = "/workspaces/gvc0/src/main/resources/runtime.c0: 150.53-150.71",
  [409] = "/workspaces/gvc0/src/main/resources/runtime.c0: 150.21-150.75",
  [475] = "src/test/resources/runtime-analysis/list.verified.c0: 27.3-27.46",
  [483] = "src/test/resources/runtime-analysis/list.verified.c0: 34.26-34.36",
  [484] = "src/test/resources/runtime-analysis/list.verified.c0: 34.5-34.43",
  [485] = "src/test/resources/runtime-analysis/list.verified.c0: 35.26-35.36",
  [486] = "src/test/resources/runtime-analysis/list.verified.c0: 35.5-35.43",
  [487] = "src/test/resources/runtime-analysis/list.verified.c0: 36.25-36.36",
  [488] = "src/test/resources/runtime-analysis/list.verified.c0: 36.43-36.53",
  [489] = "src/test/resources/runtime-analysis/list.verified.c0: 36.5-36.76",
  [498] = "src/test/resources/runtime-analysis/list.verified.c0: 44.26-44.36",
  [499] = "src/test/resources/runtime-analysis/list.verified.c0: 44.5-44.43",
  [500] = "src/test/resources/runtime-analysis/list.verified.c0: 45.26-45.36",
  [501] = "src/test/resources/runtime-analysis/list.verified.c0: 45.5-45.43",
  [502] = "src/test/resources/runtime-analysis/list.verified.c0: 46.25-46.36",
  [503] = "src/test/resources/runtime-analysis/list.verified.c0: 46.43-46.53",
  [504] = "src/test/resources/runtime-analysis/list.verified.c0: 46.5-46.76",
  [516] = "src/test/resources/runtime-analysis/list.verified.c0: 62.32-62.39",
  [517] = "src/test/resources/runtime-analysis/list.verified.c0: 62.47-62.53",
  [518] = "src/test/resources/runtime-analysis/list.verified.c0: 62.7-62.84",
  [552] = "src/test/resources/runtime-analysis/list.verified.c0: 96.45-96.51",
  [557] = "src/test/resources/runtime-analysis/list.verified.c0: 96.9-96.117",
  [562] = "src/test/resources/runtime-analysis/list.verified.c0: 100.45-100.51",
  [567] = "src/test/resources/runtime-analysis/list.verified.c0: 100.9-100.118",
  [570] = "src/test/resources/runtime-analysis/list.verified.c0: 104.16-104.22",
  [571] = "src/test/resources/runtime-analysis/list.verified.c0: 104.9-104.33",
  [572] = "src/test/resources/runtime-analysis/list.verified.c0: 105.25-105.32",
  [573] = "src/test/resources/runtime-analysis/list.verified.c0: 105.37-105.43",
  [574] = "src/test/resources/runtime-analysis/list.verified.c0: 105.9-105.64",
  [579] = "src/test/resources/runtime-analysis/list.verified.c0: 112.37-112.66",
  [580] = "src/test/resources/runtime-analysis/list.verified.c0: 112.21-112.67",
  [585] = "src/test/resources/runtime-analysis/list.verified.c0: 115.45-115.51",
  [590] = "src/test/resources/runtime-analysis/list.verified.c0: 115.9-115.118",
  [595] = "src/test/resources/runtime-analysis/list.verified.c0: 119.45-119.51",
  [600] = "src/test/resources/runtime-analysis/list.verified.c0: 119.9-119.118",
  [605] = "src/test/resources/runtime-analysis/list.verified.c0: 123.45-123.51",
  [610] = "src/test/resources/runtime-analysis/list.verified.c0: 123.9-123.117",
  [615] = "src/test/resources/runtime-analysis/list.verified.c0: 127.45-127.51",
  [620] = "src/test/resources/runtime-analysis/list.verified.c0: 127.9-127.117",
  [623] = "src/test/resources/runtime-analysis/list.verified.c0: 131.9-131.30",
  [624] = "src/test/resources/runtime-analysis/list.verified.c0: 132.16-132.22",
  [625] = "src/test/resources/runtime-analysis/list.verified.c0: 132.9-132.33",
  [628] = "src/test/resources/runtime-analysis/list.verified.c0: 136.9-136.30",
  [633] = "src/test/resources/runtime-analysis/list.verified.c0: 140.55-140.61",
  [638] = "src/test/resources/runtime-analysis/list.verified.c0: 140.9-140.126",
  [641] = "src/test/resources/runtime-analysis/list.verified.c0: 141.55-141.61",
  [646] = "src/test/resources/runtime-analysis/list.verified.c0: 141.9-141.127",
  [651] = "src/test/resources/runtime-analysis/list.verified.c0: 145.55-145.61",
  [656] = "src/test/resources/runtime-analysis/list.verified.c0: 145.9-145.126",
  [659] = "src/test/resources/runtime-analysis/list.verified.c0: 146.55-146.61",
  [664] = "src/test/resources/runtime-analysis/list.verified.c0: 146.9-146.127",
  [668] = "src/test/resources/runtime-analysis/list.verified.c0: 150.27-150.34",
  [669] = "src/test/resources/runtime-analysis/list.verified.c0: 150.42-150.48",
  [670] = "src/test/resources/runtime-analysis/list.verified.c0: 150.7-150.82",
  [674] = "src/test/resources/runtime-analysis/list.verified.c0: 153.45-153.51",
  [679] = "src/test/resources/runtime-analysis/list.verified.c0: 153.9-153.117",
  [684] = "src/test/resources/runtime-analysis/list.verified.c0: 157.45-157.51",
  [689] = "src/test/resources/runtime-analysis/list.verified.c0: 157.9-157.118",
  [692] = "src/test/resources/runtime-analysis/list.verified.c0: 161.16-161.22",
  [693] = "src/test/resources/runtime-analysis/list.verified.c0: 161.9-161.33",
  [694] = "src/test/resources/runtime-analysis/list.verified.c0: 162.25-162.32",
  [695] = "src/test/resources/runtime-analysis/list.verified.c0: 162.37-162.43",
  [696] = "src/test/resources/runtime-analysis/list.verified.c0: 162.9-162.64",
  [699] = "src/test/resources/runtime-analysis/list.verified.c0: 166.9-166.31",
  [705] = "src/test/resources/runtime-analysis/list.verified.c0: 172.34-172.63",
  [706] = "src/test/resources/runtime-analysis/list.verified.c0: 172.18-172.64",
  [711] = "src/test/resources/runtime-analysis/list.verified.c0: 175.41-175.47",
  [716] = "src/test/resources/runtime-analysis/list.verified.c0: 175.5-175.113",
  [721] = "src/test/resources/runtime-analysis/list.verified.c0: 179.41-179.47",
  [726] = "src/test/resources/runtime-analysis/list.verified.c0: 179.5-179.114",
  [727] = "src/test/resources/runtime-analysis/list.verified.c0: 180.5-180.26",
  [728] = "src/test/resources/runtime-analysis/list.verified.c0: 181.12-181.18",
  [729] = "src/test/resources/runtime-analysis/list.verified.c0: 181.5-181.29",
  [734] = "src/test/resources/runtime-analysis/list.verified.c0: 185.52-185.58",
  [739] = "src/test/resources/runtime-analysis/list.verified.c0: 185.5-185.123",
  [742] = "src/test/resources/runtime-analysis/list.verified.c0: 186.52-186.58",
  [747] = "src/test/resources/runtime-analysis/list.verified.c0: 186.5-186.124",
  [756] = "src/test/resources/runtime-analysis/list.verified.c0: 194.3-194.9",
  [757] = "src/test/resources/runtime-analysis/list.verified.c0: 194.12-194.29",
  [758] = "src/test/resources/runtime-analysis/list.verified.c0: 194.3-194.29",
  [759] = "src/test/resources/runtime-analysis/list.verified.c0: 195.23-195.40",
  [760] = "src/test/resources/runtime-analysis/list.verified.c0: 195.3-195.44",
  [762] = "src/test/resources/runtime-analysis/list.verified.c0: 196.3-196.9",
  [763] = "src/test/resources/runtime-analysis/list.verified.c0: 196.3-196.15",
  [765] = "src/test/resources/runtime-analysis/list.verified.c0: 197.3-197.10",
  [766] = "src/test/resources/runtime-analysis/list.verified.c0: 197.3-197.17",
  [796] = "src/test/resources/runtime-analysis/list.verified.c0: 226.3-226.33",
  [804] = "src/test/resources/runtime-analysis/list.verified.c0: 228.74-228.83",
  [816] = "src/test/resources/runtime-analysis/list.verified.c0: 229.30-229.39",
  [823] = "src/test/resources/runtime-analysis/list.verified.c0: 232.5-232.11",
  [824] = "src/test/resources/runtime-analysis/list.verified.c0: 232.14-232.43",
  [825] = "src/test/resources/runtime-analysis/list.verified.c0: 232.5-232.43",
  [827] = "src/test/resources/runtime-analysis/list.verified.c0: 233.5-233.11",
  [828] = "src/test/resources/runtime-analysis/list.verified.c0: 233.5-233.17",
  [830] = "src/test/resources/runtime-analysis/list.verified.c0: 234.5-234.12",
  [831] = "src/test/resources/runtime-analysis/list.verified.c0: 234.5-234.19",
  [837] = "src/test/resources/runtime-analysis/list.verified.c0: 240.34-240.44",
  [847] = "src/test/resources/runtime-analysis/list.verified.c0: 243.34-243.44",
  [857] = "src/test/resources/runtime-analysis/list.verified.c0: 244.36-244.46",
  [863] = "src/test/resources/runtime-analysis/list.verified.c0: 244.78-244.88",
  [864] = "src/test/resources/runtime-analysis/list.verified.c0: 244.78-244.93",
  [870] = "src/test/resources/runtime-analysis/list.verified.c0: 244.105-244.115",
  [878] = "src/test/resources/runtime-analysis/list.verified.c0: 245.12-245.22",
  [880] = "src/test/resources/runtime-analysis/list.verified.c0: 245.34-245.44",
  [881] = "src/test/resources/runtime-analysis/list.verified.c0: 245.34-245.49",
  [891] = "src/test/resources/runtime-analysis/list.verified.c0: 248.14-248.24",
  [901] = "src/test/resources/runtime-analysis/list.verified.c0: 260.29-260.39",
  [902] = "src/test/resources/runtime-analysis/list.verified.c0: 260.53-260.62",
  [903] = "src/test/resources/runtime-analysis/list.verified.c0: 260.64-260.73",
  [904] = "src/test/resources/runtime-analysis/list.verified.c0: 260.75-260.84",
  [905] = "src/test/resources/runtime-analysis/list.verified.c0: 260.86-260.95",
  [906] = "src/test/resources/runtime-analysis/list.verified.c0: 260.9-260.110",
  [912] = "src/test/resources/runtime-analysis/list.verified.c0: 265.48-265.57",
  [917] = "src/test/resources/runtime-analysis/list.verified.c0: 265.9-265.123",
  [920] = "src/test/resources/runtime-analysis/list.verified.c0: 266.48-266.57",
  [925] = "src/test/resources/runtime-analysis/list.verified.c0: 266.9-266.124",
  [928] = "src/test/resources/runtime-analysis/list.verified.c0: 270.25-270.35",
  [929] = "src/test/resources/runtime-analysis/list.verified.c0: 270.43-270.52",
  [930] = "src/test/resources/runtime-analysis/list.verified.c0: 270.54-270.63",
  [931] = "src/test/resources/runtime-analysis/list.verified.c0: 270.9-270.78",
  [937] = "src/test/resources/runtime-analysis/list.verified.c0: 275.48-275.57",
  [942] = "src/test/resources/runtime-analysis/list.verified.c0: 275.9-275.124",
  [945] = "src/test/resources/runtime-analysis/list.verified.c0: 276.48-276.57",
  [950] = "src/test/resources/runtime-analysis/list.verified.c0: 276.9-276.123",
  [954] = "src/test/resources/runtime-analysis/list.verified.c0: 278.37-278.47",
  [961] = "src/test/resources/runtime-analysis/list.verified.c0: 280.37-280.66",
  [962] = "src/test/resources/runtime-analysis/list.verified.c0: 280.21-280.67",
  [969] = "src/test/resources/runtime-analysis/list.verified.c0: 281.209-281.219",
  [979] = "src/test/resources/runtime-analysis/list.verified.c0: 281.430-281.440",
  [991] = "src/test/resources/runtime-analysis/list.verified.c0: 281.661-281.671",
  [1003] = "src/test/resources/runtime-analysis/list.verified.c0: 281.892-281.902",
  [1012] = "src/test/resources/runtime-analysis/list.verified.c0: 283.33-283.43",
  [1014] = "src/test/resources/runtime-analysis/list.verified.c0: 283.54-283.64",
  [1015] = "src/test/resources/runtime-analysis/list.verified.c0: 283.54-283.69",
  [1020] = "src/test/resources/runtime-analysis/list.verified.c0: 283.9-283.135",
  [1022] = "src/test/resources/runtime-analysis/list.verified.c0: 284.33-284.43",
  [1024] = "src/test/resources/runtime-analysis/list.verified.c0: 284.54-284.64",
  [1025] = "src/test/resources/runtime-analysis/list.verified.c0: 284.54-284.69",
  [1030] = "src/test/resources/runtime-analysis/list.verified.c0: 284.9-284.136",
  [1033] = "src/test/resources/runtime-analysis/list.verified.c0: 288.16-288.25",
  [1034] = "src/test/resources/runtime-analysis/list.verified.c0: 288.9-288.34",
  [1035] = "src/test/resources/runtime-analysis/list.verified.c0: 289.31-289.40",
  [1036] = "src/test/resources/runtime-analysis/list.verified.c0: 289.9-289.55",
  [1043] = "src/test/resources/runtime-analysis/list.verified.c0: 291.209-291.219",
  [1053] = "src/test/resources/runtime-analysis/list.verified.c0: 291.430-291.440",
  [1065] = "src/test/resources/runtime-analysis/list.verified.c0: 291.661-291.671",
  [1077] = "src/test/resources/runtime-analysis/list.verified.c0: 291.892-291.902",
  [1085] = "src/test/resources/runtime-analysis/list.verified.c0: 293.25-293.35",
  [1086] = "src/test/resources/runtime-analysis/list.verified.c0: 293.25-293.41",
  [1087] = "src/test/resources/runtime-analysis/list.verified.c0: 293.49-293.59",
  [1088] = "src/test/resources/runtime-analysis/list.verified.c0: 293.49-293.64",
  [1089] = "src/test/resources/runtime-analysis/list.verified.c0: 293.9-293.83",
  [1093] = "src/test/resources/runtime-analysis/list.verified.c0: 295.56-295.65",
  [1098] = "src/test/resources/runtime-analysis/list.verified.c0: 295.7-295.130",
  [1101] = "src/test/resources/runtime-analysis/list.verified.c0: 296.56-296.65",
  [1106] = "src/test/resources/runtime-analysis/list.verified.c0: 296.7-296.131",
  [1107] = "src/test/resources/runtime-analysis/list.verified.c0: 297.33-297.42",
  [1108] = "src/test/resources/runtime-analysis/list.verified.c0: 297.7-297.56",
  [1109] = "src/test/resources/runtime-analysis/list.verified.c0: 298.13-298.23",
  [1112] = "src/test/resources/runtime-analysis/list.verified.c0: 300.43-300.53",
  [1114] = "src/test/resources/runtime-analysis/list.verified.c0: 300.64-300.74",
  [1115] = "src/test/resources/runtime-analysis/list.verified.c0: 300.64-300.79",
  [1120] = "src/test/resources/runtime-analysis/list.verified.c0: 300.9-300.145",
  [1122] = "src/test/resources/runtime-analysis/list.verified.c0: 301.43-301.53",
  [1124] = "src/test/resources/runtime-analysis/list.verified.c0: 301.64-301.74",
  [1125] = "src/test/resources/runtime-analysis/list.verified.c0: 301.64-301.79",
  [1130] = "src/test/resources/runtime-analysis/list.verified.c0: 301.9-301.144",
  [1131] = "src/test/resources/runtime-analysis/list.verified.c0: 302.29-302.39",
  [1132] = "src/test/resources/runtime-analysis/list.verified.c0: 302.29-302.45",
  [1133] = "src/test/resources/runtime-analysis/list.verified.c0: 302.53-302.63",
  [1134] = "src/test/resources/runtime-analysis/list.verified.c0: 302.53-302.68",
  [1135] = "src/test/resources/runtime-analysis/list.verified.c0: 302.9-302.86",
  [1141] = "src/test/resources/runtime-analysis/list.verified.c0: 306.5-306.13",
  [1142] = "src/test/resources/runtime-analysis/list.verified.c0: 306.16-306.45",
  [1143] = "src/test/resources/runtime-analysis/list.verified.c0: 306.5-306.45",
  [1145] = "src/test/resources/runtime-analysis/list.verified.c0: 307.5-307.13",
  [1146] = "src/test/resources/runtime-analysis/list.verified.c0: 307.5-307.19",
  [1148] = "src/test/resources/runtime-analysis/list.verified.c0: 308.5-308.14",
  [1149] = "src/test/resources/runtime-analysis/list.verified.c0: 308.17-308.27",
  [1150] = "src/test/resources/runtime-analysis/list.verified.c0: 308.5-308.27",
  [1152] = "src/test/resources/runtime-analysis/list.verified.c0: 309.5-309.15",
  [1153] = "src/test/resources/runtime-analysis/list.verified.c0: 309.5-309.21",
  [1156] = "src/test/resources/runtime-analysis/list.verified.c0: 315.30-315.40",
  [1157] = "src/test/resources/runtime-analysis/list.verified.c0: 315.48-315.57",
  [1158] = "src/test/resources/runtime-analysis/list.verified.c0: 315.59-315.68",
  [1159] = "src/test/resources/runtime-analysis/list.verified.c0: 315.7-315.83",
  [1161] = "src/test/resources/runtime-analysis/list.verified.c0: 318.31-318.37",
  [1162] = "src/test/resources/runtime-analysis/list.verified.c0: 318.9-318.41",
  [1163] = "src/test/resources/runtime-analysis/list.verified.c0: 319.31-319.37",
  [1164] = "src/test/resources/runtime-analysis/list.verified.c0: 319.9-319.41",
  [1167] = "src/test/resources/runtime-analysis/list.verified.c0: 323.31-323.40",
  [1168] = "src/test/resources/runtime-analysis/list.verified.c0: 323.9-323.44",
  [1169] = "src/test/resources/runtime-analysis/list.verified.c0: 324.31-324.40",
  [1170] = "src/test/resources/runtime-analysis/list.verified.c0: 324.9-324.44",
  [1171] = "src/test/resources/runtime-analysis/list.verified.c0: 325.32-325.42",
  [1172] = "src/test/resources/runtime-analysis/list.verified.c0: 325.47-325.56",
  [1173] = "src/test/resources/runtime-analysis/list.verified.c0: 325.9-325.75",
  [1175] = "src/test/resources/runtime-analysis/list.verified.c0: 327.32-327.42",
  [1176] = "src/test/resources/runtime-analysis/list.verified.c0: 327.56-327.65",
  [1177] = "src/test/resources/runtime-analysis/list.verified.c0: 327.67-327.76",
  [1178] = "src/test/resources/runtime-analysis/list.verified.c0: 327.82-327.111",
  [1179] = "src/test/resources/runtime-analysis/list.verified.c0: 327.7-327.112",
  [1180] = "src/test/resources/runtime-analysis/list.verified.c0: 328.27-328.37",
  [1181] = "src/test/resources/runtime-analysis/list.verified.c0: 328.42-328.51",
  [1182] = "src/test/resources/runtime-analysis/list.verified.c0: 328.7-328.70",
  [1184] = "src/test/resources/runtime-analysis/list.verified.c0: 331.30-331.36",
  [1185] = "src/test/resources/runtime-analysis/list.verified.c0: 331.9-331.43",
  [1186] = "src/test/resources/runtime-analysis/list.verified.c0: 332.30-332.36",
  [1187] = "src/test/resources/runtime-analysis/list.verified.c0: 332.9-332.43",
  [1204] = "src/test/resources/runtime-analysis/list.verified.c0: 349.7-349.39",
  [1208] = "src/test/resources/runtime-analysis/list.verified.c0: 353.19-353.52",
  [1210] = "src/test/resources/runtime-analysis/list.verified.c0: 354.10-354.40",
  [1223] = "src/test/resources/runtime-analysis/list.verified.c0: 365.27-365.37",
  [1224] = "src/test/resources/runtime-analysis/list.verified.c0: 365.5-365.41",
  [1225] = "src/test/resources/runtime-analysis/list.verified.c0: 366.27-366.37",
  [1226] = "src/test/resources/runtime-analysis/list.verified.c0: 366.5-366.41",
  [1227] = "src/test/resources/runtime-analysis/list.verified.c0: 367.28-367.39",
  [1228] = "src/test/resources/runtime-analysis/list.verified.c0: 367.46-367.56",
  [1229] = "src/test/resources/runtime-analysis/list.verified.c0: 367.5-367.79",
  [1240] = "src/test/resources/runtime-analysis/list.verified.c0: 375.56-375.66",
  [1245] = "src/test/resources/runtime-analysis/list.verified.c0: 375.5-375.131",
  [1248] = "src/test/resources/runtime-analysis/list.verified.c0: 376.56-376.66",
  [1253] = "src/test/resources/runtime-analysis/list.verified.c0: 376.5-376.132",
  [1254] = "src/test/resources/runtime-analysis/list.verified.c0: 377.25-377.36",
  [1255] = "src/test/resources/runtime-analysis/list.verified.c0: 377.43-377.53",
  [1256] = "src/test/resources/runtime-analysis/list.verified.c0: 377.5-377.76",
  [1267] = "src/test/resources/runtime-analysis/list.verified.c0: 385.56-385.66",
  [1272] = "src/test/resources/runtime-analysis/list.verified.c0: 385.5-385.131",
  [1275] = "src/test/resources/runtime-analysis/list.verified.c0: 386.56-386.66",
  [1280] = "src/test/resources/runtime-analysis/list.verified.c0: 386.5-386.132",
  [1281] = "src/test/resources/runtime-analysis/list.verified.c0: 387.25-387.36",
  [1282] = "src/test/resources/runtime-analysis/list.verified.c0: 387.43-387.53",
  [1283] = "src/test/resources/runtime-analysis/list.verified.c0: 387.5-387.76",
  [1292] = "src/test/resources/runtime-analysis/list.verified.c0: 395.5-395.18",
  [1296] = "src/test/resources/runtime-analysis/list.verified.c0: 399.45-399.55",
  [1301] = "src/test/resources/runtime-analysis/list.verified.c0: 399.5-399.121",
  [1304] = "src/test/resources/runtime-analysis/list.verified.c0: 400.45-400.55",
  [1309] = "src/test/resources/runtime-analysis/list.verified.c0: 400.5-400.122",
  [1310] = "src/test/resources/runtime-analysis/list.verified.c0: 401.21-401.32",
  [1311] = "src/test/resources/runtime-analysis/list.verified.c0: 401.39-401.49",
  [1312] = "src/test/resources/runtime-analysis/list.verified.c0: 401.5-401.72",
  [1322] = "src/test/resources/runtime-analysis/list.verified.c0: 411.7-411.20",
  [1324] = "src/test/resources/runtime-analysis/list.verified.c0: 415.7-415.30",
  [1329] = "src/test/resources/runtime-analysis/list.verified.c0: 420.45-420.55",
  [1334] = "src/test/resources/runtime-analysis/list.verified.c0: 420.5-420.121",
  [1337] = "src/test/resources/runtime-analysis/list.verified.c0: 421.45-421.55",
  [1342] = "src/test/resources/runtime-analysis/list.verified.c0: 421.5-421.122",
  [1343] = "src/test/resources/runtime-analysis/list.verified.c0: 422.12-422.22",
  [1344] = "src/test/resources/runtime-analysis/list.verified.c0: 422.5-422.32",
  [1345] = "src/test/resources/runtime-analysis/list.verified.c0: 423.21-423.32",
  [1346] = "src/test/resources/runtime-analysis/list.verified.c0: 423.39-423.49",
  [1347] = "src/test/resources/runtime-analysis/list.verified.c0: 423.5-423.72"
};
