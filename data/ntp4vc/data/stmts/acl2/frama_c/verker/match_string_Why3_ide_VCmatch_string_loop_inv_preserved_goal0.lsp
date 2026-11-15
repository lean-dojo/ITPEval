;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/match_string_Why3_ide_VCmatch_string_loop_inv_preserved_goal0:
;; preservation of the match-string loop invariant giving lower and upper
;; bounds on the current index under the source memory, string, comparison,
;; and quantified prefix hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mslip0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mslip0-address-base (address)
  (car address))

(defun mslip0-address-offset (address)
  (cdr address))

(defun mslip0-shift (address amount)
  (cons
   (mslip0-address-base address)
   (+ (mslip0-address-offset address) amount)))

(defun mslip0-null-address ()
  (cons 0 0))

;; Conservative interfaces for the arbitrary pointer memory t_2, character
;; memory t_1, allocation map t, region function, and logical string
;; operations from the source context.

(defstub mslip0-pointer-memory (address) t)
(defstub mslip0-character-memory (address) t)
(defstub mslip0-allocation (index) t)
(defstub mslip0-region (base) t)
(defstub mslip0-l-strncmp (left right count) t)
(defstub mslip0-l-strlen (address) t)
(defstub mslip0-l-real-len (address count) t)
(defstub mslip0-to-uint8 (value) t)
(defstub mslip0-to-sint8 (value) t)
(defstub mslip0-to-uint64 (value) t)
(defstub mslip0-to-sint64 (value) t)
(defstub mslip0-linked-op () t)
(defstub mslip0-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; integer domains.

(defun-sk mslip0-function-types-p ()
  (forall (address index base left right count)
    (and
     (implies
      (mslip0-address-p address)
      (and
       (mslip0-address-p
        (mslip0-pointer-memory address))
       (integerp
        (mslip0-character-memory address))
       (integerp
        (mslip0-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (mslip0-allocation index)))
     (implies
      (integerp base)
      (integerp
       (mslip0-region base)))
     (implies
      (and
       (mslip0-address-p left)
       (mslip0-address-p right)
       (integerp count))
      (integerp
       (mslip0-l-strncmp left right count)))
     (implies
      (and
       (mslip0-address-p address)
       (integerp count))
      (integerp
       (mslip0-l-real-len address count))))))

(defun mslip0-linked-p ()
  (if (mslip0-linked-op) t nil))

(defun mslip0-sconst-p ()
  (if (mslip0-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun mslip0-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun mslip0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun mslip0-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun mslip0-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun mslip0-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this verification condition.

(defun-sk mslip0-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (mslip0-is-uint8-p
       (mslip0-to-uint8 value))
      (implies
       (mslip0-is-uint8-p value)
       (equal
        (mslip0-to-uint8 value)
        value))
      (equal
       (mslip0-to-uint8
        (mslip0-to-uint8 value))
       (mslip0-to-uint8 value))))))

(defun-sk mslip0-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (mslip0-is-uint64-p
       (mslip0-to-uint64 value))
      (implies
       (mslip0-is-uint64-p value)
       (equal
        (mslip0-to-uint64 value)
        value))
      (equal
       (mslip0-to-uint64
        (mslip0-to-uint64 value))
       (mslip0-to-uint64 value))))))

(defun-sk mslip0-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (mslip0-is-sint8-p
       (mslip0-to-sint8 value))
      (implies
       (mslip0-is-sint8-p value)
       (equal
        (mslip0-to-sint8 value)
        value))
      (equal
       (mslip0-to-sint8
        (mslip0-to-sint8 value))
       (mslip0-to-sint8 value))))))

(defun-sk mslip0-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (mslip0-is-sint64-p
       (mslip0-to-sint64 value))
      (implies
       (mslip0-is-sint64-p value)
       (equal
        (mslip0-to-sint64 value)
        value))
      (equal
       (mslip0-to-sint64
        (mslip0-to-sint64 value))
       (mslip0-to-sint64 value))))))

(defun-sk mslip0-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (mslip0-to-sint8
        (mslip0-to-uint8 value))
       (mslip0-to-sint8 value))
      (equal
       (mslip0-to-sint64
        (mslip0-to-uint64 value))
       (mslip0-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the fixed allocation map t.

(defun mslip0-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (mslip0-address-base address))
    (<= 0
        (mslip0-address-offset address))
    (<=
     (+ (mslip0-address-offset address)
        length)
     (mslip0-allocation
      (mslip0-address-base address))))))

;; Exact unfolding of Memory.framed for the pointer memory t_2.

(defun-sk mslip0-framed-p ()
  (forall (address)
    (implies
     (mslip0-address-p address)
     (<=
      (mslip0-region
       (mslip0-address-base
        (mslip0-pointer-memory address)))
      0))))

;; Exact unfolding of A_Strlen.p_valid_str. Its terminating index remains an
;; internal existential over all mathematical integers.

(defun-sk mslip0-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (mslip0-is-sint8-p
       (mslip0-character-memory
        (mslip0-shift address position)))))))

(defun-sk mslip0-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (mslip0-character-memory
       (mslip0-shift address index))
      0)
     (mslip0-is-uint64-p index)
     (mslip0-valid-rw-p
      (mslip0-shift address 0)
      (+ 1 index))
     (mslip0-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk mslip0-strlen-laws-p ()
  (forall (address)
    (implies
     (mslip0-address-p address)
     (and
      (if
          (equal
           (mslip0-character-memory
            (mslip0-shift address 0))
           0)
          (equal
           (mslip0-l-strlen address)
           0)
        (equal
         (mslip0-to-uint64
          (+ 1
             (mslip0-l-strlen
              (mslip0-shift address 1))))
         (mslip0-l-strlen address)))
      (mslip0-is-uint64-p
       (mslip0-l-strlen address))))))

;; A_StrCmp.l_cmp and l_strcmp, with the universal closure of the source
;; fixpoint equation for l_strncmp_1'.

(defun mslip0-l-cmp (left right)
  (if (equal right left)
      0
    (if (< left right)
        -1
      1)))

(defun mslip0-l-strcmp (left right)
  (mslip0-l-strncmp
   left
   right
   (mslip0-l-strlen left)))

(defun-sk mslip0-strncmp-law-p ()
  (forall (left right count)
    (implies
     (and
      (mslip0-address-p left)
      (mslip0-address-p right)
      (integerp count))
     (if
         (equal count -1)
         (equal
          (mslip0-l-strncmp left right count)
          0)
       (if
           (equal
            (mslip0-character-memory
             (mslip0-shift right 0))
            (mslip0-character-memory
             (mslip0-shift left 0)))
           (equal
            (mslip0-l-strncmp
             (mslip0-shift left 1)
             (mslip0-shift right 1)
             (- count 1))
            (mslip0-l-strncmp left right count))
         (equal
          (mslip0-l-cmp
           (mslip0-to-uint8
            (mslip0-character-memory
             (mslip0-shift left 0)))
           (mslip0-to-uint8
            (mslip0-character-memory
             (mslip0-shift right 0))))
          (mslip0-l-strncmp left right count)))))))

;; Universal closures of A_MatchString.fix_l_real_len and Q_TL_real_len.

(defun-sk mslip0-real-len-laws-p ()
  (forall (address count)
    (implies
     (and
      (mslip0-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (mslip0-pointer-memory
             (mslip0-shift address 0))
            (mslip0-null-address)))
          (equal
           (mslip0-l-real-len address count)
           0)
        (equal
         (mslip0-to-uint64
          (+ 1
             (mslip0-l-real-len
              (mslip0-shift address 1)
              (mslip0-to-uint64
               (- count 1)))))
         (mslip0-l-real-len address count)))
      (mslip0-is-uint64-p
       (mslip0-l-real-len address count))))))

(defun mslip0-int-min (left right)
  (if (< left right)
      left
    right))

;; The four quantified loop hypotheses retain their internal universal scope
;; over all mathematical integers.

(defun-sk mslip0-prior-strings-valid-p
    (a1 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (mslip0-valid-string-p
        (mslip0-pointer-memory
         (mslip0-shift a1 index))))))))

(defun-sk mslip0-prior-characters-equal-p
    (left right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (equal
        (mslip0-character-memory
         (mslip0-shift left index))
        (mslip0-character-memory
         (mslip0-shift right index))))))))

(defun-sk mslip0-prior-comparisons-nonzero-p
    (a1 right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (not
        (equal
         (mslip0-l-strcmp
          (mslip0-pointer-memory
           (mslip0-shift a1 index))
          right)
         0)))))))

(defun-sk mslip0-real-prefix-strings-valid-p
    (a1 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (implies
        (mslip0-is-uint64-p index)
        (mslip0-valid-string-p
         (mslip0-pointer-memory
          (mslip0-shift a1 index)))))))))

(defun-sk
    ntp4vc-match-string-loop-inv-preserved-goal0-statement ()
  (forall
   (a1 i1 a i2 i i3 i4)
   (implies
    (and
     (mslip0-address-p a1)
     (integerp i1)
     (mslip0-address-p a)
     (integerp i2)
     (integerp i)
     (integerp i3)
     (integerp i4)
     (mslip0-function-types-p)
     (mslip0-to-uint8-laws-p)
     (mslip0-to-uint64-laws-p)
     (mslip0-to-sint8-laws-p)
     (mslip0-to-sint64-laws-p)
     (mslip0-signed-unsigned-projection-laws-p)
     (mslip0-strlen-laws-p)
     (mslip0-strncmp-law-p)
     (mslip0-real-len-laws-p))
    (let*
        ((a2
          (mslip0-pointer-memory
           (mslip0-shift a1 i1)))
         (x
          (mslip0-l-strcmp a2 a))
         (x1
          (mslip0-character-memory
           (mslip0-shift a2 i2)))
         (x2
          (mslip0-character-memory
           (mslip0-shift a i2)))
         (x3
          (mslip0-l-real-len a1 i))
         (x4
          (mslip0-l-strlen a2))
         (a3
          (mslip0-shift a1 0)))
      (implies
       (and
        (not
         (equal a2
                (mslip0-null-address)))
        (not
         (equal x 0))
        (not
         (equal x1 x2))
        (not
         (equal
          (mslip0-character-memory
           (mslip0-shift a2 i3))
          (mslip0-character-memory
           (mslip0-shift a i3))))
        (not
         (equal
          (mslip0-character-memory
           (mslip0-shift a2 i4))
          (mslip0-character-memory
           (mslip0-shift a i4))))
        (<= 0 i1)
        (<= 0 i2)
        (<= 0 i3)
        (<= 0 i4)
        (< (mslip0-to-uint64 i1) i)
        (<=
         (mslip0-region
          (mslip0-address-base a))
         0)
        (<=
         (mslip0-region
          (mslip0-address-base a1))
         0)
        (<= x3 i)
        (<= i1 x3)
        (<= i2 x4)
        (<= i3 x4)
        (<=
         i4
         (mslip0-int-min
          (mslip0-l-strlen a)
          x4))
        (<= i 2147483647)
        (mslip0-framed-p)
        (mslip0-linked-p)
        (mslip0-sconst-p)
        (mslip0-is-sint32-p i1)
        (mslip0-is-uint64-p i)
        (mslip0-is-uint64-p i4)
        (mslip0-valid-string-p a)
        (mslip0-is-sint32-p
         (+ 1 i1))
        (mslip0-valid-string-p a2)
        (mslip0-is-sint32-p x)
        (if
            (< (mslip0-to-uint8 x1)
               (mslip0-to-uint8 x2))
            (equal x -1)
          (equal x 1))
        (implies
         (equal x3 i)
         (mslip0-valid-rw-p a3 i))
        (implies
         (< x3 i)
         (mslip0-valid-rw-p
          a3
          (+ 1 x3)))
        (or
         (equal x -1)
         (equal x 1))
        (mslip0-prior-strings-valid-p
         a1 i1)
        (mslip0-prior-characters-equal-p
         a2 a i2)
        (mslip0-prior-comparisons-nonzero-p
         a1 a i1)
        (mslip0-real-prefix-strings-valid-p
         a1 x3))
       (and
        (< i1 x3)
        (<= -1 i1)))))))

(value-triple :itpeval-statement-checked)

:q
