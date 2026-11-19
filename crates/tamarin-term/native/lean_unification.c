#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

/* The generated module initializer and export use the pinned Lean ABI. */
extern lean_object *initialize_tamarin_x2dspec_TamarinRuntime(uint8_t builtin);
extern uint8_t tamarin_flat_ac_equal(lean_object *lhs, lean_object *rhs);
extern lean_object *tamarin_flat_ac_residual(lean_object *tail, lean_object *rhs);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

/* Serialized exactly once by Rust's OnceLock, before any worker calls Lean. */
uint8_t tamarin_lean_initialize(void) {
    lean_object *result = initialize_tamarin_x2dspec_TamarinRuntime(1);
    if (!lean_io_result_is_ok(result)) {
        lean_dec(result);
        return 1;
    }
    lean_dec(result);
    lean_io_mark_end_initialization();
    return 0;
}

void tamarin_lean_thread_initialize(void) { lean_initialize_thread(); }
void tamarin_lean_thread_finalize(void) { lean_finalize_thread(); }

static lean_object *atom_array(const uint64_t *atoms, size_t length) {
    lean_object *array = lean_alloc_array(length, length);
    for (size_t i = 0; i < length; ++i) {
        lean_array_set_core(array, i, lean_box_uint64(atoms[i]));
    }
    return array;
}

extern lean_object *tamarin_operand_refine(lean_object *sides);

size_t tamarin_lean_operand_refine(const uint64_t *sides, size_t count, uint64_t *indices) {
    lean_object *result = tamarin_operand_refine(atom_array(sides, count));
    size_t n = lean_array_size(result);
    if (n <= count / 2) {
        for (size_t i = 0; i < n; ++i)
            indices[i] = lean_unbox_uint64(lean_array_get_core(result, i));
    } else {
        n = SIZE_MAX;
    }
    lean_dec(result);
    return n;
}

extern uint8_t tamarin_residual_rigid(uint8_t lk, uint64_t lh, lean_object *ls,
                                     uint8_t rk, uint64_t rh, lean_object *rs);

uint8_t tamarin_lean_residual_rigid(uint8_t lk, uint64_t lh, const uint64_t *ls, size_t nl,
                                    uint8_t rk, uint64_t rh, const uint64_t *rs, size_t nr) {
    return tamarin_residual_rigid(lk, lh, atom_array(ls, nl), rk, rh, atom_array(rs, nr));
}

extern uint8_t tamarin_residual_variable(uint8_t right, uint64_t key, uint64_t key_sort,
                                         uint8_t kind, uint64_t value_sort, lean_object *ids);

uint8_t tamarin_lean_residual_variable(uint8_t right, uint64_t key, uint64_t key_sort, uint8_t kind,
                                      uint64_t value_sort, const uint64_t *ids, size_t count) {
    return tamarin_residual_variable(right, key, key_sort, kind, value_sort, atom_array(ids, count));
}

extern lean_object *tamarin_cancel_common(lean_object *left, lean_object *right);
uint8_t tamarin_lean_cancel_common(const uint64_t *left, size_t left_size,
                                   const uint64_t *right, size_t right_size,
                                   uint64_t *left_out, size_t *left_len,
                                   uint64_t *right_out, size_t *right_len) {
    lean_object *result = tamarin_cancel_common(atom_array(left, left_size), atom_array(right, right_size));
    if (lean_array_size(result) != 2) {
        lean_dec(result);
        return 255;
    }
    lean_object *l = lean_array_get_core(result, 0);
    lean_object *r = lean_array_get_core(result, 1);
    *left_len = lean_array_size(l);
    *right_len = lean_array_size(r);
    if (*left_len > left_size || *right_len > right_size) {
        lean_dec(result);
        return 255;
    }
    for (size_t i = 0; i < *left_len; i++)
        left_out[i] = lean_unbox_uint64(lean_array_get_core(l, i));
    for (size_t i = 0; i < *right_len; i++)
        right_out[i] = lean_unbox_uint64(lean_array_get_core(r, i));
    lean_dec(result);
    return 0;
}

extern uint8_t tamarin_constructor_variant(lean_object *roots, lean_object *used);
extern uint8_t tamarin_ground_variant(lean_object *holes, lean_object *anchors,
                                      lean_object *deps, uint8_t rigid);
uint8_t tamarin_lean_ground_variant(const uint64_t *holes, size_t hole_count,
                                    const uint64_t *anchors, size_t anchor_count,
                                    const uint64_t *deps, size_t dep_count, uint8_t rigid) {
    return tamarin_ground_variant(atom_array(holes, hole_count), atom_array(anchors, anchor_count),
                                  atom_array(deps, dep_count), rigid);
}

extern uint8_t tamarin_exclude_root(lean_object *rows, lean_object *args);

uint8_t tamarin_lean_exclude_root(const uint64_t *words, size_t row_count,
                                  const uint64_t *args, size_t arity) {
    lean_object *rows = lean_alloc_array(row_count, row_count);
    for (size_t i = 0; i < row_count; ++i)
        lean_array_set_core(rows, i, atom_array(words + i * arity, arity));
    return tamarin_exclude_root(rows, atom_array(args, arity));
}

uint8_t tamarin_lean_constructor_variant(const uint64_t *roots, size_t root_count,
                                        const uint64_t *used, size_t used_count) {
    return tamarin_constructor_variant(atom_array(roots, root_count), atom_array(used, used_count));
}

extern uint8_t tamarin_sort_clash(lean_object *left, lean_object *right);
uint8_t tamarin_lean_sort_clash(const uint64_t *left, size_t left_count,
                               const uint64_t *right, size_t right_count) {
    return tamarin_sort_clash(atom_array(left, left_count), atom_array(right, right_count));
}

extern lean_object *tamarin_reduce_rule_slot(uint64_t slot, lean_object *keys, lean_object *subjects);
uint8_t tamarin_lean_reduce_rule_slot(uint64_t slot, const uint64_t *keys,
                                     const uint64_t *subjects, size_t length, uint64_t *out) {
    lean_object *result = tamarin_reduce_rule_slot(slot, atom_array(keys, length),
                                                 atom_array(subjects, length));
    size_t count = lean_array_size(result);
    if (count == 1) *out = lean_unbox_uint64(lean_array_get_core(result, 0));
    lean_dec(result);
    return count > 1 ? 255 : (uint8_t)count;
}

/* The exported Lean function consumes both arrays. No Lean object or owned
 * allocation crosses back into Rust. The input slices remain Rust-owned. */
uint8_t tamarin_lean_flat_ac_equal(const uint64_t *lhs, size_t lhs_length,
                                 const uint64_t *rhs, size_t rhs_length) {
    return tamarin_flat_ac_equal(atom_array(lhs, lhs_length),
                                atom_array(rhs, rhs_length));
}

/* Output is [status, residual atoms...] in Lean. Copy into the caller's
 * buffer and release the array here, keeping allocation ownership local. */
uint8_t tamarin_lean_flat_ac_residual(const uint64_t *tail, size_t tail_length,
                                    const uint64_t *rhs, size_t rhs_length,
                                    uint64_t *residual, size_t capacity,
                                    size_t *residual_length) {
    *residual_length = 0;
    lean_object *result = tamarin_flat_ac_residual(atom_array(tail, tail_length),
                                                 atom_array(rhs, rhs_length));
    size_t length = lean_array_size(result);
    if (length == 0) {
        lean_dec(result);
        return 255;
    }
    uint64_t status = lean_unbox_uint64(lean_array_get_core(result, 0));
    size_t count = length - 1;
    if (status > 2 || count > capacity || (status == 2 && count == 0) ||
        (status != 2 && count != 0)) {
        lean_dec(result);
        return 255;
    }
    for (size_t i = 0; i < count; ++i) {
        residual[i] = lean_unbox_uint64(lean_array_get_core(result, i + 1));
    }
    *residual_length = count;
    lean_dec(result);
    return (uint8_t)status;
}

/* Nested numeric rows avoid textual serialization and variable-name parsing.
 * The Rust guard owns this opaque result until every requested row is copied. */
extern lean_object *tamarin_flat_ac_match(uint64_t n, lean_object *occ,
                                        lean_object *tail, lean_object *rhs);
void *tamarin_lean_flat_ac_match(uint64_t n,
                               const uint64_t *occ, size_t occ_length,
                               const uint64_t *tail, size_t tail_length,
                               const uint64_t *rhs, size_t rhs_length) {
    return tamarin_flat_ac_match(n, atom_array(occ, occ_length),
                                atom_array(tail, tail_length), atom_array(rhs, rhs_length));
}
size_t tamarin_lean_match_count(const void *result) {
    return lean_array_size((lean_object *)result);
}
size_t tamarin_lean_match_rows(const void *result, size_t answer) {
    lean_object *answers = (lean_object *)result;
    if (answer >= lean_array_size(answers)) return SIZE_MAX;
    return lean_array_size(lean_array_get_core(answers, answer));
}
uint8_t tamarin_lean_match_row(const void *result, size_t answer, size_t variable,
                             uint64_t *out, size_t capacity, size_t *length) {
    *length = 0;
    lean_object *answers = (lean_object *)result;
    if (answer >= lean_array_size(answers)) return 255;
    lean_object *rows = lean_array_get_core(answers, answer);
    if (variable >= lean_array_size(rows)) return 255;
    lean_object *row = lean_array_get_core(rows, variable);
    size_t size = lean_array_size(row);
    if (size == 0 || size > capacity) return 255;
    for (size_t i = 0; i < size; ++i)
        out[i] = lean_unbox_uint64(lean_array_get_core(row, i));
    *length = size;
    return 0;
}
void tamarin_lean_match_release(void *result) { lean_dec((lean_object *)result); }

typedef struct {
    const uint64_t *data;
    size_t size;
} whole_word_slice;

extern lean_object *tamarin_whole_unify(lean_object *decls, lean_object *nodes,
                                       lean_object *equations);

extern uint8_t tamarin_check_factors(lean_object *, lean_object *, lean_object *,
                                     lean_object *, lean_object *);

static lean_object *word_rows(const whole_word_slice *rows, size_t count) {
    lean_object *nodes = lean_alloc_array(count, count);
    for (size_t i = 0; i < count; ++i)
        lean_array_set_core(nodes, i, atom_array(rows[i].data, rows[i].size));
    return nodes;
}

extern lean_object *tamarin_select_joined_variants(lean_object *rows);
uint8_t tamarin_lean_select_joined_variants(const whole_word_slice *rows, size_t count,
                                           uint8_t *mask) {
    lean_object *reply = tamarin_select_joined_variants(word_rows(rows, count));
    if (lean_is_scalar(reply)) return 0;
    lean_object *flags = lean_ctor_get(reply, 0);
    uint8_t status = 255;
    if (lean_array_size(flags) == count) {
        status = 1;
        for (size_t i = 0; i < count; ++i) {
            uint64_t flag = lean_unbox_uint64(lean_array_get_core(flags, i));
            if (flag > 1) { status = 255; break; }
            mask[i] = (uint8_t)flag;
        }
    }
    lean_dec(reply);
    return status;
}

extern uint8_t tamarin_exclude_ac_factors(lean_object *, lean_object *);
uint8_t tamarin_lean_exclude_ac_factors(const whole_word_slice *rows, size_t count,
                                       whole_word_slice heads) {
    return tamarin_exclude_ac_factors(word_rows(rows, count), atom_array(heads.data, heads.size));
}

uint8_t tamarin_lean_check_factors(whole_word_slice decls, const whole_word_slice *rows,
                                   size_t count, whole_word_slice original,
                                   whole_word_slice bindings, whole_word_slice residual) {
    return tamarin_check_factors(atom_array(decls.data, decls.size), word_rows(rows, count),
        atom_array(original.data, original.size), atom_array(bindings.data, bindings.size),
        atom_array(residual.data, residual.size));
}

/* All input rows are borrowed for this call only. The Lean export consumes
 * its copies. The current reply format has exactly one row and one word. */
uint8_t tamarin_lean_whole_unify(whole_word_slice decls, const whole_word_slice *rows,
                                 size_t count, whole_word_slice equations) {
    lean_object *nodes = word_rows(rows, count);
    lean_object *result = tamarin_whole_unify(atom_array(decls.data, decls.size), nodes,
        atom_array(equations.data, equations.size));
    uint8_t status = 255;
    if (lean_array_size(result) == 1) {
        lean_object *row = lean_array_get_core(result, 0);
        if (lean_array_size(row) == 1) {
            uint64_t word = lean_unbox_uint64(lean_array_get_core(row, 0));
            if (word <= 2) status = (uint8_t)word;
        }
    }
    lean_dec(result);
    return status;
}

extern lean_object *tamarin_operand_unify(uint64_t width, lean_object *sides);

extern lean_object *tamarin_project_answers(uint64_t width, lean_object *answers);

typedef struct {
    uint8_t status;
    void *arms;
} projected_answers;

/* Transfer the Option.some field's reference to the caller. */
static lean_object *take_some(lean_object *option) {
    lean_object *value = lean_ctor_get(option, 0);
    lean_inc(value);
    lean_dec(option);
    return value;
}

extern lean_object *tamarin_open_match_select(uint64_t rigid, uint64_t subject);

/* Transfer the row array into the same opaque row reader as flat matching. */
static void *wrap_rows(lean_object *rows) {
    lean_object *outer = lean_alloc_array(1, 1);
    lean_array_set_core(outer, 0, rows);
    return outer;
}

static void *selection_rows(lean_object *reply) {
    return lean_is_scalar(reply) ? NULL : wrap_rows(take_some(reply));
}

extern lean_object *tamarin_binary_cancellation_rows(lean_object *unit);

void *tamarin_lean_binary_cancellation_rows(void) {
    return wrap_rows(tamarin_binary_cancellation_rows(lean_box(0)));
}

extern lean_object *tamarin_mixed_cancellation_rows(lean_object *unit);

void *tamarin_lean_mixed_cancellation_rows(void) {
    return wrap_rows(tamarin_mixed_cancellation_rows(lean_box(0)));
}

extern lean_object *tamarin_xor_matchings(uint64_t width);

void *tamarin_lean_xor_matchings(uint64_t width) {
    return selection_rows(tamarin_xor_matchings(width));
}

extern lean_object *tamarin_dh_exponent_images(lean_object *unit);

void *tamarin_lean_dh_exponent_images(void) {
    return wrap_rows(tamarin_dh_exponent_images(lean_box(0)));
}

void *tamarin_lean_open_match_select(uint64_t rigid, uint64_t subject) {
    return selection_rows(tamarin_open_match_select(rigid, subject));
}

extern lean_object *tamarin_dh_tower_images(uint64_t width);

void *tamarin_lean_dh_tower_images(uint64_t width) {
    return selection_rows(tamarin_dh_tower_images(width));
}

extern lean_object *tamarin_ac_pivot(uint64_t size);

void *tamarin_lean_ac_pivot(uint64_t size) {
    return selection_rows(tamarin_ac_pivot(size));
}

extern lean_object *tamarin_dh_peer_images(uint8_t power);

void *tamarin_lean_dh_peer_images(void) {
    return selection_rows(tamarin_dh_peer_images(1));
}

extern lean_object *tamarin_ac_subgroups(uint64_t size);

void *tamarin_lean_ac_subgroups(uint64_t size) {
    return selection_rows(tamarin_ac_subgroups(size));
}

extern lean_object *tamarin_sorted_ac_match(uint64_t ac_sort, lean_object *variable_sorts,
                                          lean_object *atom_sorts, lean_object *occurrences,
                                          lean_object *tail, lean_object *rhs);

void *tamarin_lean_sorted_ac_match(uint64_t ac_sort, whole_word_slice variable_sorts,
                                   whole_word_slice atom_sorts, whole_word_slice occurrences,
                                   whole_word_slice tail, whole_word_slice rhs) {
    lean_object *reply = tamarin_sorted_ac_match(ac_sort, atom_array(variable_sorts.data, variable_sorts.size),
        atom_array(atom_sorts.data, atom_sorts.size), atom_array(occurrences.data, occurrences.size),
        atom_array(tail.data, tail.size), atom_array(rhs.data, rhs.size));
    return lean_is_scalar(reply) ? NULL : take_some(reply);
}

/* Solver deferral and invalid solver output have distinct statuses. A
 * successful projection transfers one array reference, even for zero arms. */
static projected_answers project_answers(uint64_t width, lean_object *option) {
    if (lean_is_scalar(option)) return (projected_answers){0, NULL};
    lean_object *projected = tamarin_project_answers(width, take_some(option));
    if (lean_is_scalar(projected)) return (projected_answers){255, NULL};
    return (projected_answers){1, take_some(projected)};
}

projected_answers tamarin_lean_operand_unify(uint64_t width, const whole_word_slice *sides, size_t count) {
    return project_answers(width, tamarin_operand_unify(width, word_rows(sides, count)));
}

extern lean_object *tamarin_graph_homogeneous_unify(uint64_t width, uint64_t symbol, uint64_t sort,
                                                     lean_object *decls, lean_object *nodes,
                                                     lean_object *equations);

projected_answers tamarin_lean_graph_homogeneous_unify(uint64_t width, uint64_t symbol, uint64_t sort,
                                                       whole_word_slice decls, const whole_word_slice *rows,
                                                       size_t count, whole_word_slice equations) {
    return project_answers(width, tamarin_graph_homogeneous_unify(width, symbol, sort,
        atom_array(decls.data, decls.size), word_rows(rows, count),
        atom_array(equations.data, equations.size)));
}

size_t tamarin_lean_match_row_size(const void *result, size_t arm, size_t index) {
    if (arm >= tamarin_lean_match_count(result)) return SIZE_MAX;
    lean_object *rows = lean_array_get_core((lean_object *)result, arm);
    if (index >= lean_array_size(rows)) return SIZE_MAX;
    return lean_array_size(lean_array_get_core(rows, index));
}
