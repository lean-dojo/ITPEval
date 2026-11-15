;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/match_string_Why3_ide_VCmatch_string_missing_post_goal11:
;; the match-string missing-result condition forces the sentinel index -22
;; under the source memory, string-validity, comparison, framing, and
;; quantified prefix hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun msmp11-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun msmp11-address-base (address)
  (car address))

(defun msmp11-address-offset (address)
  (cdr address))

(defun msmp11-shift (address amount)
  (cons
   (msmp11-address-base address)
   (+ (msmp11-address-offset address) amount)))

(defun msmp11-null-address ()
  (cons 0 0))

;; Conservative interfaces for the arbitrary pointer memory t_2, character
;; memory t_1, allocation map t, region function, and source logical string
;; operations and predicates.

(defstub msmp11-pointer-memory (address) t)
(defstub msmp11-character-memory (address) t)
(defstub msmp11-allocation (index) t)
(defstub msmp11-region (base) t)
(defstub msmp11-l-strncmp (left right count) t)
(defstub msmp11-l-strlen (address) t)
(defstub msmp11-l-real-len (address count) t)
(defstub msmp11-to-uint8 (value) t)
(defstub msmp11-to-sint8 (value) t)
(defstub msmp11-to-uint64 (value) t)
(defstub msmp11-to-sint64 (value) t)
(defstub msmp11-linked-op () t)
(defstub msmp11-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; integer domains.

(defun-sk msmp11-function-types-p ()
  (forall (address index base left right count)
    (and
     (implies
      (msmp11-address-p address)
      (and
       (msmp11-address-p (msmp11-pointer-memory address))
       (integerp (msmp11-character-memory address))
       (integerp (msmp11-l-strlen address))))
     (implies
      (integerp index)
      (integerp (msmp11-allocation index)))
     (implies
      (integerp base)
      (integerp (msmp11-region base)))
     (implies
      (and
       (msmp11-address-p left)
       (msmp11-address-p right)
       (integerp count))
      (integerp (msmp11-l-strncmp left right count)))
     (implies
      (and
       (msmp11-address-p address)
       (integerp count))
      (integerp (msmp11-l-real-len address count))))))

(defun msmp11-linked-p ()
  (if (msmp11-linked-op) t nil))

(defun msmp11-sconst-p ()
  (if (msmp11-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun msmp11-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun msmp11-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun msmp11-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun msmp11-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun msmp11-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions.

(defun-sk msmp11-to-uint-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (msmp11-is-uint8-p
       (msmp11-to-uint8 value))
      (msmp11-is-uint64-p
       (msmp11-to-uint64 value))
      (implies
       (msmp11-is-uint8-p value)
       (equal
        (msmp11-to-uint8 value)
        value))
      (implies
       (msmp11-is-uint64-p value)
       (equal
        (msmp11-to-uint64 value)
        value))
      (equal
       (msmp11-to-uint8
        (msmp11-to-uint8 value))
       (msmp11-to-uint8 value))
      (equal
       (msmp11-to-uint64
        (msmp11-to-uint64 value))
       (msmp11-to-uint64 value))))))

(defun-sk msmp11-to-sint-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (msmp11-is-sint8-p
       (msmp11-to-sint8 value))
      (msmp11-is-sint64-p
       (msmp11-to-sint64 value))
      (implies
       (msmp11-is-sint8-p value)
       (equal
        (msmp11-to-sint8 value)
        value))
      (implies
       (msmp11-is-sint64-p value)
       (equal
        (msmp11-to-sint64 value)
        value))
      (equal
       (msmp11-to-sint8
        (msmp11-to-sint8 value))
       (msmp11-to-sint8 value))
      (equal
       (msmp11-to-sint64
        (msmp11-to-sint64 value))
       (msmp11-to-sint64 value))))))

;; Exact proj_int8 and proj_int64 interactions from the source context.

(defun-sk msmp11-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (msmp11-to-sint8
        (msmp11-to-uint8 value))
       (msmp11-to-sint8 value))
      (equal
       (msmp11-to-sint64
        (msmp11-to-uint64 value))
       (msmp11-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the fixed allocation map t.

(defun msmp11-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (msmp11-address-base address))
    (<= 0 (msmp11-address-offset address))
    (<=
     (+ (msmp11-address-offset address) length)
     (msmp11-allocation (msmp11-address-base address))))))

;; Exact unfolding of Memory.framed for the pointer memory t_2.

(defun-sk msmp11-framed-p ()
  (forall (address)
    (implies
     (msmp11-address-p address)
     (<=
      (msmp11-region
       (msmp11-address-base
        (msmp11-pointer-memory address)))
      0))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating index remains an
;; internal existential over all mathematical integers.

(defun-sk msmp11-string-chars-sint8-through-p (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (msmp11-is-sint8-p
       (msmp11-character-memory
        (msmp11-shift address position)))))))

(defun-sk msmp11-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (msmp11-character-memory
       (msmp11-shift address index))
      0)
     (msmp11-is-uint64-p index)
     (msmp11-valid-rw-p
      (msmp11-shift address 0)
      (+ 1 index))
     (msmp11-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk msmp11-strlen-laws-p ()
  (forall (address)
    (implies
     (msmp11-address-p address)
     (and
      (if
          (equal
           (msmp11-character-memory
            (msmp11-shift address 0))
           0)
          (equal (msmp11-l-strlen address) 0)
        (equal
         (msmp11-to-uint64
          (+ 1
             (msmp11-l-strlen
              (msmp11-shift address 1))))
         (msmp11-l-strlen address)))
      (msmp11-is-uint64-p
       (msmp11-l-strlen address))))))

;; A_StrCmp.l_cmp and l_strcmp, with the universal closure of the source
;; fixpoint equation for l_strncmp_1'.

(defun msmp11-l-cmp (left right)
  (if (equal right left)
      0
    (if (< left right)
        -1
      1)))

(defun msmp11-l-strcmp (left right)
  (msmp11-l-strncmp
   left
   right
   (msmp11-l-strlen left)))

(defun-sk msmp11-strncmp-law-p ()
  (forall (left right count)
    (implies
     (and
      (msmp11-address-p left)
      (msmp11-address-p right)
      (integerp count))
     (if
         (equal count -1)
         (equal
          (msmp11-l-strncmp left right count)
          0)
       (if
           (equal
            (msmp11-character-memory
             (msmp11-shift right 0))
            (msmp11-character-memory
             (msmp11-shift left 0)))
           (equal
            (msmp11-l-strncmp
             (msmp11-shift left 1)
             (msmp11-shift right 1)
             (- count 1))
            (msmp11-l-strncmp left right count))
         (equal
          (msmp11-l-cmp
           (msmp11-to-uint8
            (msmp11-character-memory
             (msmp11-shift left 0)))
           (msmp11-to-uint8
            (msmp11-character-memory
             (msmp11-shift right 0))))
          (msmp11-l-strncmp left right count)))))))

;; Universal closures of A_MatchString.fix_l_real_len and Q_TL_real_len.

(defun-sk msmp11-real-len-laws-p ()
  (forall (address count)
    (implies
     (and
      (msmp11-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (msmp11-pointer-memory
             (msmp11-shift address 0))
            (msmp11-null-address)))
          (equal
           (msmp11-l-real-len address count)
           0)
        (equal
         (msmp11-to-uint64
          (+ 1
             (msmp11-l-real-len
              (msmp11-shift address 1)
              (msmp11-to-uint64 (- count 1)))))
         (msmp11-l-real-len address count)))
      (msmp11-is-uint64-p
       (msmp11-l-real-len address count))))))

;; The source's five quantified loop and string-equality hypotheses retain
;; their internal universal scope.

(defun-sk msmp11-prior-strings-valid-p (a1 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (msmp11-valid-string-p
        (msmp11-pointer-memory
         (msmp11-shift a1 index))))))))

(defun-sk msmp11-prior-comparisons-nonzero-p (a1 right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (not
        (equal
         (msmp11-l-strcmp
          (msmp11-pointer-memory
           (msmp11-shift a1 index))
          right)
         0)))))))

(defun-sk msmp11-real-prefix-strings-valid-p (a1 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (implies
        (msmp11-is-uint64-p index)
        (msmp11-valid-string-p
         (msmp11-pointer-memory
          (msmp11-shift a1 index)))))))))

(defun-sk msmp11-real-prefix-comparisons-nonzero-p
    (a1 right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (implies
        (msmp11-is-uint64-p index)
        (not
         (equal
          (msmp11-l-strcmp
           (msmp11-pointer-memory
            (msmp11-shift a1 index))
           right)
          0))))))))

(defun-sk msmp11-strings-equal-or-outside-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (or
      (equal
       (msmp11-character-memory
        (msmp11-shift left index))
       (msmp11-character-memory
        (msmp11-shift right index)))
      (< index 0)
      (< (msmp11-l-strlen left) index)))))

(defun-sk ntp4vc-match-string-missing-post-goal11-statement ()
  (forall
   (a1 i1 i a)
   (implies
    (and
     (msmp11-address-p a1)
     (integerp i1)
     (integerp i)
     (msmp11-address-p a)
     (msmp11-function-types-p)
     (msmp11-to-uint-laws-p)
     (msmp11-to-sint-laws-p)
     (msmp11-signed-unsigned-projection-laws-p)
     (msmp11-strlen-laws-p)
     (msmp11-strncmp-law-p)
     (msmp11-real-len-laws-p))
    (let*
        ((a2
          (msmp11-pointer-memory
           (msmp11-shift a1 i1)))
         (x
          (msmp11-l-real-len a1 i))
         (a3
          (msmp11-shift a1 0)))
      (implies
       (and
        (not
         (equal a2 (msmp11-null-address)))
        (equal
         (msmp11-l-strcmp a2 a)
         0)
        (<= 0 i1)
        (< (msmp11-to-uint64 i1) i)
        (<= (msmp11-region (msmp11-address-base a)) 0)
        (<= (msmp11-region (msmp11-address-base a1)) 0)
        (<= x i)
        (<= i1 x)
        (<= i 2147483647)
        (msmp11-framed-p)
        (msmp11-linked-p)
        (msmp11-sconst-p)
        (msmp11-is-sint32-p i1)
        (msmp11-is-uint64-p i)
        (msmp11-valid-string-p a)
        (msmp11-valid-string-p a2)
        (implies
         (equal x i)
         (msmp11-valid-rw-p a3 i))
        (implies
         (< x i)
         (msmp11-valid-rw-p a3 (+ 1 x)))
        (msmp11-prior-strings-valid-p a1 i1)
        (msmp11-prior-comparisons-nonzero-p a1 a i1)
        (msmp11-real-prefix-strings-valid-p a1 x)
        (msmp11-real-prefix-comparisons-nonzero-p
         a1 a x)
        (msmp11-strings-equal-or-outside-p a2 a))
       (equal i1 -22))))))

(value-triple :itpeval-statement-checked)

:q
