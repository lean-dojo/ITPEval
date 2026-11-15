;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/match_string_Why3_ide_VCmatch_string_assert_goal4:
;; validity of the non-null string selected at an in-range match-string index,
;; under the verification condition's memory, length, framing, linkedness,
;; comparison, and prefix-validity hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ms4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ms4-address-base (address)
  (car address))

(defun ms4-address-offset (address)
  (cdr address))

(defun ms4-shift (address amount)
  (cons
   (ms4-address-base address)
   (+ (ms4-address-offset address) amount)))

(defun ms4-null-address ()
  (cons 0 0))

;; Conservative interfaces for the arbitrary pointer memory t_2, character
;; memory t_1, allocation map t, region function, and logical string
;; functions from the source context.

(defstub ms4-pointer-memory (address) t)
(defstub ms4-character-memory (address) t)
(defstub ms4-allocation (index) t)
(defstub ms4-region (base) t)
(defstub ms4-l-strncmp (left right count) t)
(defstub ms4-l-strlen (address) t)
(defstub ms4-l-real-len (address count) t)
(defstub ms4-linked-op () t)
(defstub ms4-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; integer domains.

(defun-sk ms4-function-types-p ()
  (forall (address index base left right count)
    (and
     (implies
      (ms4-address-p address)
      (and
       (ms4-address-p (ms4-pointer-memory address))
       (integerp (ms4-character-memory address))
       (integerp (ms4-l-strlen address))))
     (implies
      (integerp index)
      (integerp (ms4-allocation index)))
     (implies
      (integerp base)
      (integerp (ms4-region base)))
     (implies
      (and
       (ms4-address-p left)
       (ms4-address-p right)
       (integerp count))
      (integerp (ms4-l-strncmp left right count)))
     (implies
      (and
       (ms4-address-p address)
       (integerp count))
      (integerp (ms4-l-real-len address count))))))

(defun ms4-linked-p ()
  (if (ms4-linked-op) t nil))

(defun ms4-sconst-p ()
  (if (ms4-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun ms4-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun ms4-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun ms4-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun ms4-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun ms4-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Conservative interfaces and the source's explicit range, identity,
;; projection, and signed/unsigned projection laws for the conversions used
;; by the string recurrences.

(defstub ms4-to-uint8 (value) t)
(defstub ms4-to-sint8 (value) t)
(defstub ms4-to-uint64 (value) t)
(defstub ms4-to-sint64 (value) t)

(defun-sk ms4-uint8-conversion-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ms4-is-uint8-p (ms4-to-uint8 value))
      (implies
       (ms4-is-uint8-p value)
       (equal (ms4-to-uint8 value) value))
      (equal
       (ms4-to-uint8 (ms4-to-uint8 value))
       (ms4-to-uint8 value))))))

(defun-sk ms4-sint8-conversion-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ms4-is-sint8-p (ms4-to-sint8 value))
      (implies
       (ms4-is-sint8-p value)
       (equal (ms4-to-sint8 value) value))
      (equal
       (ms4-to-sint8 (ms4-to-sint8 value))
       (ms4-to-sint8 value))))))

(defun-sk ms4-uint64-conversion-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ms4-is-uint64-p (ms4-to-uint64 value))
      (implies
       (ms4-is-uint64-p value)
       (equal (ms4-to-uint64 value) value))
      (equal
       (ms4-to-uint64 (ms4-to-uint64 value))
       (ms4-to-uint64 value))))))

(defun-sk ms4-sint64-conversion-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ms4-is-sint64-p (ms4-to-sint64 value))
      (implies
       (ms4-is-sint64-p value)
       (equal (ms4-to-sint64 value) value))
      (equal
       (ms4-to-sint64 (ms4-to-sint64 value))
       (ms4-to-sint64 value))))))

(defun-sk ms4-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (ms4-to-sint8 (ms4-to-uint8 value))
       (ms4-to-sint8 value))
      (equal
       (ms4-to-sint64 (ms4-to-uint64 value))
       (ms4-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the fixed allocation map t.

(defun ms4-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (ms4-address-base address))
    (<= 0 (ms4-address-offset address))
    (<=
     (+ (ms4-address-offset address) length)
     (ms4-allocation (ms4-address-base address))))))

;; Exact unfolding of Memory.framed for the pointer memory t_2.

(defun-sk ms4-framed-p ()
  (forall (address)
    (implies
     (ms4-address-p address)
     (<=
      (ms4-region
       (ms4-address-base
        (ms4-pointer-memory address)))
      0))))

;; Exact unfolding of A_Strlen.p_valid_str. Its terminating index remains an
;; internal existential over all mathematical integers.

(defun-sk ms4-string-chars-sint8-through-p (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (ms4-is-sint8-p
       (ms4-character-memory
        (ms4-shift address position)))))))

(defun-sk ms4-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (ms4-character-memory
       (ms4-shift address index))
      0)
     (ms4-is-uint64-p index)
     (ms4-valid-rw-p
      (ms4-shift address 0)
      (+ 1 index))
     (ms4-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk ms4-strlen-laws-p ()
  (forall (address)
    (implies
     (ms4-address-p address)
     (and
      (if
          (equal
           (ms4-character-memory
            (ms4-shift address 0))
           0)
          (equal (ms4-l-strlen address) 0)
        (equal
         (ms4-to-uint64
          (+ 1
             (ms4-l-strlen
              (ms4-shift address 1))))
         (ms4-l-strlen address)))
      (ms4-is-uint64-p
       (ms4-l-strlen address))))))

;; A_StrCmp.l_cmp and l_strcmp, with the universal closure of the source
;; fixpoint equation for l_strncmp_1'.

(defun ms4-l-cmp (left right)
  (if (equal right left)
      0
    (if (< left right)
        -1
      1)))

(defun ms4-l-strcmp (left right)
  (ms4-l-strncmp
   left
   right
   (ms4-l-strlen left)))

(defun-sk ms4-strncmp-law-p ()
  (forall (left right count)
    (implies
     (and
      (ms4-address-p left)
      (ms4-address-p right)
      (integerp count))
     (if
         (equal count -1)
         (equal
          (ms4-l-strncmp left right count)
          0)
       (if
           (equal
            (ms4-character-memory
             (ms4-shift right 0))
            (ms4-character-memory
             (ms4-shift left 0)))
           (equal
            (ms4-l-strncmp
             (ms4-shift left 1)
             (ms4-shift right 1)
             (- count 1))
            (ms4-l-strncmp left right count))
         (equal
          (ms4-l-cmp
           (ms4-to-uint8
            (ms4-character-memory
             (ms4-shift left 0)))
           (ms4-to-uint8
            (ms4-character-memory
             (ms4-shift right 0))))
          (ms4-l-strncmp left right count)))))))

;; Universal closures of A_MatchString.fix_l_real_len and Q_TL_real_len.

(defun-sk ms4-real-len-laws-p ()
  (forall (address count)
    (implies
     (and
      (ms4-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (ms4-pointer-memory
             (ms4-shift address 0))
            (ms4-null-address)))
          (equal
           (ms4-l-real-len address count)
           0)
        (equal
         (ms4-to-uint64
          (+ 1
             (ms4-l-real-len
              (ms4-shift address 1)
              (ms4-to-uint64 (- count 1)))))
         (ms4-l-real-len address count)))
      (ms4-is-uint64-p
       (ms4-l-real-len address count))))))

;; The three quantified loop hypotheses retain their internal universal scope.

(defun-sk ms4-prior-strings-valid-p (a1 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (ms4-valid-string-p
        (ms4-pointer-memory
         (ms4-shift a1 index))))))))

(defun-sk ms4-prior-comparisons-nonzero-p (a1 right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (not
        (equal
         (ms4-l-strcmp
          (ms4-pointer-memory
           (ms4-shift a1 index))
          right)
         0)))))))

(defun-sk ms4-real-prefix-strings-valid-p (a1 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (implies
        (ms4-is-uint64-p index)
        (ms4-valid-string-p
         (ms4-pointer-memory
          (ms4-shift a1 index)))))))))

(defun-sk ntp4vc-match-string-assert-goal4-statement ()
  (forall
   (a1 i1 i a)
   (implies
    (and
     (ms4-address-p a1)
     (integerp i1)
     (integerp i)
     (ms4-address-p a)
     (ms4-function-types-p)
     (ms4-uint8-conversion-laws-p)
     (ms4-sint8-conversion-laws-p)
     (ms4-uint64-conversion-laws-p)
     (ms4-sint64-conversion-laws-p)
     (ms4-signed-unsigned-projection-laws-p)
     (ms4-strlen-laws-p)
     (ms4-strncmp-law-p)
     (ms4-real-len-laws-p))
    (let*
        ((a2
          (ms4-pointer-memory
           (ms4-shift a1 i1)))
         (x
          (ms4-l-real-len a1 i))
         (a3
          (ms4-shift a1 0)))
      (implies
       (and
        (not (equal a2 (ms4-null-address)))
        (<= 0 i1)
        (< (ms4-to-uint64 i1) i)
        (<= (ms4-region (ms4-address-base a)) 0)
        (<= (ms4-region (ms4-address-base a1)) 0)
        (<= x i)
        (<= i1 x)
        (<= i 2147483647)
        (ms4-framed-p)
        (ms4-linked-p)
        (ms4-sconst-p)
        (ms4-is-sint32-p i1)
        (ms4-is-uint64-p i)
        (ms4-valid-string-p a)
        (implies
         (equal x i)
         (ms4-valid-rw-p a3 i))
        (implies
         (< x i)
         (ms4-valid-rw-p a3 (+ 1 x)))
        (ms4-prior-strings-valid-p a1 i1)
        (ms4-prior-comparisons-nonzero-p a1 a i1)
        (ms4-real-prefix-strings-valid-p a1 x))
       (ms4-valid-string-p a2))))))

(value-triple :itpeval-statement-checked)

:q
