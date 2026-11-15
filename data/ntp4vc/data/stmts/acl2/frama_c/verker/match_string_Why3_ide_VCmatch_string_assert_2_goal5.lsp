;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/match_string_Why3_ide_VCmatch_string_assert_2_goal5:
;; existence of a bounded unsigned index at which two valid strings differ,
;; under the match-string verification condition's memory, length, comparison,
;; framing, linkedness, and prefix hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ms5-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ms5-address-base (address)
  (car address))

(defun ms5-address-offset (address)
  (cdr address))

(defun ms5-shift (address amount)
  (cons
   (ms5-address-base address)
   (+ (ms5-address-offset address) amount)))

(defun ms5-null-address ()
  (cons 0 0))

;; Conservative interfaces for the arbitrary pointer memory t_2, character
;; memory t_1, allocation map t, region function, and the source's logical
;; string functions, C integer conversions, and predicates.

(defstub ms5-pointer-memory (address) t)
(defstub ms5-character-memory (address) t)
(defstub ms5-allocation (index) t)
(defstub ms5-region (base) t)
(defstub ms5-l-strncmp (left right count) t)
(defstub ms5-l-strlen (address) t)
(defstub ms5-l-real-len (address count) t)
(defstub ms5-to-uint8 (value) t)
(defstub ms5-to-sint8 (value) t)
(defstub ms5-to-uint64 (value) t)
(defstub ms5-to-sint64 (value) t)
(defstub ms5-linked-op () t)
(defstub ms5-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; integer domains.

(defun-sk ms5-function-types-p ()
  (forall (address index base left right count)
    (and
     (implies
      (ms5-address-p address)
      (and
       (ms5-address-p (ms5-pointer-memory address))
       (integerp (ms5-character-memory address))
       (integerp (ms5-l-strlen address))))
     (implies
      (integerp index)
      (integerp (ms5-allocation index)))
     (implies
      (integerp base)
      (integerp (ms5-region base)))
     (implies
      (and
       (ms5-address-p left)
       (ms5-address-p right)
       (integerp count))
      (integerp (ms5-l-strncmp left right count)))
     (implies
      (and
       (ms5-address-p address)
       (integerp count))
      (integerp (ms5-l-real-len address count))))))

(defun ms5-linked-p ()
  (if (ms5-linked-op) t nil))

(defun ms5-sconst-p ()
  (if (ms5-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun ms5-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun ms5-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun ms5-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun ms5-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun ms5-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Exact universal source laws for the abstract Cint.to_uint8 and
;; Cint.to_uint64 interfaces: range, identity on-range, and projection.

(defun-sk ms5-to-uint-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ms5-is-uint8-p
       (ms5-to-uint8 value))
      (ms5-is-uint64-p
       (ms5-to-uint64 value))
      (implies
       (ms5-is-uint8-p value)
       (equal
        (ms5-to-uint8 value)
        value))
      (implies
       (ms5-is-uint64-p value)
       (equal
        (ms5-to-uint64 value)
        value))
      (equal
       (ms5-to-uint8
        (ms5-to-uint8 value))
       (ms5-to-uint8 value))
      (equal
       (ms5-to-uint64
        (ms5-to-uint64 value))
       (ms5-to-uint64 value))))))

;; Exact universal source laws for the abstract signed conversions: range,
;; identity on-range, and projection.

(defun-sk ms5-sint8-conversion-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ms5-is-sint8-p
       (ms5-to-sint8 value))
      (implies
       (ms5-is-sint8-p value)
       (equal
        (ms5-to-sint8 value)
        value))
      (equal
       (ms5-to-sint8
        (ms5-to-sint8 value))
       (ms5-to-sint8 value))))))

(defun-sk ms5-sint64-conversion-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ms5-is-sint64-p
       (ms5-to-sint64 value))
      (implies
       (ms5-is-sint64-p value)
       (equal
        (ms5-to-sint64 value)
        value))
      (equal
       (ms5-to-sint64
        (ms5-to-sint64 value))
       (ms5-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk ms5-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (ms5-to-sint8
        (ms5-to-uint8 value))
       (ms5-to-sint8 value))
      (equal
       (ms5-to-sint64
        (ms5-to-uint64 value))
       (ms5-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the fixed allocation map t.

(defun ms5-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (ms5-address-base address))
    (<= 0 (ms5-address-offset address))
    (<=
     (+ (ms5-address-offset address) length)
     (ms5-allocation (ms5-address-base address))))))

;; Exact unfolding of Memory.framed for the pointer memory t_2.

(defun-sk ms5-framed-p ()
  (forall (address)
    (implies
     (ms5-address-p address)
     (<=
      (ms5-region
       (ms5-address-base
        (ms5-pointer-memory address)))
      0))))

;; Exact unfolding of A_Strlen.p_valid_str. Its terminating index is an
;; internal existential over all mathematical integers.

(defun-sk ms5-string-chars-sint8-through-p (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (ms5-is-sint8-p
       (ms5-character-memory
        (ms5-shift address position)))))))

(defun-sk ms5-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (ms5-character-memory
       (ms5-shift address index))
      0)
     (ms5-is-uint64-p index)
     (ms5-valid-rw-p
      (ms5-shift address 0)
      (+ 1 index))
     (ms5-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk ms5-strlen-laws-p ()
  (forall (address)
    (implies
     (ms5-address-p address)
     (and
      (if
          (equal
           (ms5-character-memory
            (ms5-shift address 0))
           0)
          (equal (ms5-l-strlen address) 0)
        (equal
         (ms5-to-uint64
          (+ 1
             (ms5-l-strlen
              (ms5-shift address 1))))
         (ms5-l-strlen address)))
      (ms5-is-uint64-p
       (ms5-l-strlen address))))))

;; A_StrCmp.l_cmp and l_strcmp, with the universal closure of the source
;; fixpoint equation for l_strncmp_1'.

(defun ms5-l-cmp (left right)
  (if (equal right left)
      0
    (if (< left right)
        -1
      1)))

(defun ms5-l-strcmp (left right)
  (ms5-l-strncmp
   left
   right
   (ms5-l-strlen left)))

(defun-sk ms5-strncmp-law-p ()
  (forall (left right count)
    (implies
     (and
      (ms5-address-p left)
      (ms5-address-p right)
      (integerp count))
     (if
         (equal count -1)
         (equal
          (ms5-l-strncmp left right count)
          0)
       (if
           (equal
            (ms5-character-memory
             (ms5-shift right 0))
            (ms5-character-memory
             (ms5-shift left 0)))
           (equal
            (ms5-l-strncmp
             (ms5-shift left 1)
             (ms5-shift right 1)
             (- count 1))
            (ms5-l-strncmp left right count))
         (equal
          (ms5-l-cmp
           (ms5-to-uint8
            (ms5-character-memory
             (ms5-shift left 0)))
           (ms5-to-uint8
            (ms5-character-memory
             (ms5-shift right 0))))
          (ms5-l-strncmp left right count)))))))

;; Universal closures of A_MatchString.fix_l_real_len and Q_TL_real_len.

(defun-sk ms5-real-len-laws-p ()
  (forall (address count)
    (implies
     (and
      (ms5-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (ms5-pointer-memory
             (ms5-shift address 0))
            (ms5-null-address)))
          (equal
           (ms5-l-real-len address count)
           0)
        (equal
         (ms5-to-uint64
          (+ 1
             (ms5-l-real-len
              (ms5-shift address 1)
              (ms5-to-uint64 (- count 1)))))
         (ms5-l-real-len address count)))
      (ms5-is-uint64-p
       (ms5-l-real-len address count))))))

;; The four quantified loop hypotheses retain their internal universal scope.

(defun-sk ms5-prior-strings-valid-p (a1 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (ms5-valid-string-p
        (ms5-pointer-memory
         (ms5-shift a1 index))))))))

(defun-sk ms5-prefix-equal-p (left right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (equal
        (ms5-character-memory
         (ms5-shift left index))
        (ms5-character-memory
         (ms5-shift right index))))))))

(defun-sk ms5-prior-comparisons-nonzero-p (a1 right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (not
        (equal
         (ms5-l-strcmp
          (ms5-pointer-memory
           (ms5-shift a1 index))
          right)
         0)))))))

(defun-sk ms5-real-prefix-strings-valid-p (a1 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (implies
        (ms5-is-uint64-p index)
        (ms5-valid-string-p
         (ms5-pointer-memory
          (ms5-shift a1 index)))))))))

(defun ms5-integer-min (left right)
  (if (<= left right)
      left
    right))

;; The requested conclusion remains an internal existential witness rather
;; than an additional external statement parameter.

(defun-sk ms5-bounded-mismatch-exists-p (left right left-length)
  (exists (index)
    (and
     (integerp index)
     (not
      (equal
       (ms5-character-memory
        (ms5-shift left index))
       (ms5-character-memory
        (ms5-shift right index))))
     (<= 0 index)
     (<=
      index
      (ms5-integer-min
       (ms5-l-strlen right)
       left-length))
     (ms5-is-uint64-p index))))

(defun-sk ntp4vc-match-string-assert-2-goal5-statement ()
  (forall
   (a1 i1 a i2 i i3)
   (implies
    (and
     (ms5-address-p a1)
     (integerp i1)
     (ms5-address-p a)
     (integerp i2)
     (integerp i)
     (integerp i3)
     (ms5-function-types-p)
     (ms5-to-uint-laws-p)
     (ms5-sint8-conversion-laws-p)
     (ms5-sint64-conversion-laws-p)
     (ms5-signed-unsigned-projection-laws-p)
     (ms5-strlen-laws-p)
     (ms5-strncmp-law-p)
     (ms5-real-len-laws-p))
    (let*
        ((a2
          (ms5-pointer-memory
           (ms5-shift a1 i1)))
         (x
          (ms5-l-strcmp a2 a))
         (x1
          (ms5-character-memory
           (ms5-shift a2 i2)))
         (x2
          (ms5-character-memory
           (ms5-shift a i2)))
         (x3
          (ms5-l-real-len a1 i))
         (x4
          (ms5-l-strlen a2))
         (a3
          (ms5-shift a1 0)))
      (implies
       (and
        (not (equal a2 (ms5-null-address)))
        (not (equal x 0))
        (not (equal x1 x2))
        (not
         (equal
          (ms5-character-memory
           (ms5-shift a2 i3))
          (ms5-character-memory
           (ms5-shift a i3))))
        (<= 0 i1)
        (<= 0 i2)
        (<= 0 i3)
        (< (ms5-to-uint64 i1) i)
        (<= (ms5-region (ms5-address-base a)) 0)
        (<= (ms5-region (ms5-address-base a1)) 0)
        (<= x3 i)
        (<= i1 x3)
        (<= i2 x4)
        (<= i3 x4)
        (<= i 2147483647)
        (ms5-framed-p)
        (ms5-linked-p)
        (ms5-sconst-p)
        (ms5-is-sint32-p i1)
        (ms5-is-uint64-p i)
        (ms5-valid-string-p a)
        (ms5-valid-string-p a2)
        (ms5-is-sint32-p x)
        (if
            (< (ms5-to-uint8 x1)
               (ms5-to-uint8 x2))
            (equal x -1)
          (equal x 1))
        (implies
         (equal x3 i)
         (ms5-valid-rw-p a3 i))
        (implies
         (< x3 i)
         (ms5-valid-rw-p a3 (+ 1 x3)))
        (or
         (equal x -1)
         (equal x 1))
        (ms5-prior-strings-valid-p a1 i1)
        (ms5-prefix-equal-p a2 a i2)
        (ms5-prior-comparisons-nonzero-p a1 a i1)
       (ms5-real-prefix-strings-valid-p a1 x3))
       (ms5-bounded-mismatch-exists-p
        a2 a x4))))))

(value-triple :itpeval-statement-checked)

:q
