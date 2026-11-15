;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_loop_inv_2_preserved_goal3:
;; preservation of the unsigned-64 loop-index invariant after incrementing
;; the shared nonzero equal-character prefix index, under the stated memory,
;; string-validity, comparison, region, linkedness, and constancy hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sslip2g3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sslip2g3-address-base (address)
  (car address))

(defun sslip2g3-address-offset (address)
  (cdr address))

(defun sslip2g3-shift (address amount)
  (cons
   (sslip2g3-address-base address)
   (+ (sslip2g3-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region, logical
;; strlen, logical strncmp, C integer conversions, linkedness, and constancy
;; symbols.

(defstub sslip2g3-character-memory (address) t)
(defstub sslip2g3-allocation (index) t)
(defstub sslip2g3-region (base) t)
(defstub sslip2g3-l-strlen (address) t)
(defstub sslip2g3-l-strncmp (left right count) t)
(defstub sslip2g3-to-uint64 (value) t)
(defstub sslip2g3-to-sint32 (value) t)
(defstub sslip2g3-linked-op () t)
(defstub sslip2g3-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sslip2g3-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (sslip2g3-address-p address)
      (and
       (integerp
        (sslip2g3-character-memory address))
       (integerp
        (sslip2g3-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sslip2g3-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sslip2g3-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sslip2g3-to-uint64 value))
       (integerp
        (sslip2g3-to-sint32 value))))
     (implies
      (and
       (sslip2g3-address-p left)
       (sslip2g3-address-p right)
       (integerp count))
      (integerp
       (sslip2g3-l-strncmp left right count))))))

(defun sslip2g3-linked-p ()
  (if (sslip2g3-linked-op) t nil))

(defun sslip2g3-sconst-p ()
  (if (sslip2g3-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sslip2g3-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sslip2g3-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sslip2g3-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by logical strlen and logical strncmp.

(defun-sk sslip2g3-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslip2g3-is-uint64-p
       (sslip2g3-to-uint64 value))
      (implies
       (sslip2g3-is-uint64-p value)
       (equal
        (sslip2g3-to-uint64 value)
        value))
      (equal
       (sslip2g3-to-uint64
        (sslip2g3-to-uint64 value))
       (sslip2g3-to-uint64 value))))))

(defun-sk sslip2g3-to-sint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslip2g3-is-sint32-p
       (sslip2g3-to-sint32 value))
      (implies
       (sslip2g3-is-sint32-p value)
       (equal
        (sslip2g3-to-sint32 value)
        value))
      (equal
       (sslip2g3-to-sint32
        (sslip2g3-to-sint32 value))
       (sslip2g3-to-sint32 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sslip2g3-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sslip2g3-address-base address))
    (<= 0
        (sslip2g3-address-offset address))
    (<=
     (+ (sslip2g3-address-offset address)
        length)
     (sslip2g3-allocation
      (sslip2g3-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its null terminator remains an
;; internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sslip2g3-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sslip2g3-is-sint8-p
       (sslip2g3-character-memory
        (sslip2g3-shift address position)))))))

(defun-sk sslip2g3-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sslip2g3-character-memory
       (sslip2g3-shift address index))
      0)
     (sslip2g3-is-uint64-p index)
     (sslip2g3-valid-rw-p
      (sslip2g3-shift address 0)
      (+ 1 index))
     (sslip2g3-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sslip2g3-strlen-laws-p ()
  (forall (address)
    (implies
     (sslip2g3-address-p address)
     (and
      (if
          (equal
           (sslip2g3-character-memory
            (sslip2g3-shift address 0))
           0)
          (equal
           (sslip2g3-l-strlen address)
           0)
        (equal
         (sslip2g3-to-uint64
          (+ 1
             (sslip2g3-l-strlen
              (sslip2g3-shift address 1))))
         (sslip2g3-l-strlen address)))
      (sslip2g3-is-uint64-p
       (sslip2g3-l-strlen address))))))

;; Universal closures of A_StrnCmp.fix_l_strncmp_2' and Q_TL_strncmp_2'.

(defun-sk sslip2g3-strncmp-laws-p ()
  (forall (left right count)
    (implies
     (and
      (sslip2g3-address-p left)
      (sslip2g3-address-p right)
      (integerp count))
     (and
      (if
          (equal count 0)
          (equal
           (sslip2g3-l-strncmp left right count)
           0)
        (if
            (equal
             (sslip2g3-character-memory
              (sslip2g3-shift right 0))
             (sslip2g3-character-memory
              (sslip2g3-shift left 0)))
            (if
                (equal
                 (sslip2g3-character-memory
                  (sslip2g3-shift left 0))
                 0)
                (equal
                 (sslip2g3-l-strncmp left right count)
                 0)
              (equal
               (sslip2g3-l-strncmp
                (sslip2g3-shift left 1)
                (sslip2g3-shift right 1)
                (sslip2g3-to-uint64 (- count 1)))
               (sslip2g3-l-strncmp left right count)))
          (equal
           (sslip2g3-to-sint32
            (-
             (sslip2g3-character-memory
              (sslip2g3-shift left 0))
             (sslip2g3-character-memory
              (sslip2g3-shift right 0))))
           (sslip2g3-l-strncmp left right count))))
      (sslip2g3-is-sint32-p
       (sslip2g3-l-strncmp left right count))))))

(defun sslip2g3-strnequal-p (left right count)
  (equal
   (sslip2g3-l-strncmp left right count)
   0))

;; The source prefix hypothesis retains its universal quantifier over every
;; mathematical integer and its original nonnegative and strict upper bounds.

(defun-sk sslip2g3-prefix-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (equal
        (sslip2g3-character-memory
         (sslip2g3-shift left position))
        (sslip2g3-character-memory
         (sslip2g3-shift right position))))))))

(defun-sk
    ntp4vc-sysfs-streq-loop-inv-2-preserved-goal3-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (sslip2g3-address-p a1)
     (integerp i)
     (sslip2g3-address-p a)
     (sslip2g3-function-types-p)
     (sslip2g3-to-uint64-laws-p)
     (sslip2g3-to-sint32-laws-p)
     (sslip2g3-strlen-laws-p)
     (sslip2g3-strncmp-laws-p))
    (let*
        ((a2
          (sslip2g3-shift a1 i))
         (x
          (sslip2g3-character-memory a2))
         (a3
          (sslip2g3-shift a i))
         (x1
          (sslip2g3-character-memory a3))
         (x2
          (+ 1 i)))
      (implies
       (and
        (not (equal x 0))
        (equal x x1)
        (<= i
            (sslip2g3-l-strlen a))
        (<= i
            (sslip2g3-l-strlen a1))
        (<=
         (sslip2g3-region
          (sslip2g3-address-base a))
         0)
        (<=
         (sslip2g3-region
          (sslip2g3-address-base a1))
         0)
        (sslip2g3-linked-p)
        (sslip2g3-sconst-p)
        (sslip2g3-is-uint64-p i)
        (sslip2g3-valid-string-p a)
        (sslip2g3-valid-string-p a1)
        (sslip2g3-strnequal-p a1 a i)
        (sslip2g3-is-sint8-p x1)
        (sslip2g3-is-sint8-p x)
        (sslip2g3-valid-string-p a3)
        (sslip2g3-valid-string-p a2)
        (sslip2g3-prefix-equal-before-p
         a1 a i))
       (equal
        x2
        (sslip2g3-to-uint64 x2)))))))

(value-triple :itpeval-statement-checked)

:q
