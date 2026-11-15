;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_loop_inv_preserved_goal2:
;; the successor of a shared nonzero equal-character prefix index is fixed by
;; unsigned-64 conversion, under the stated memory, string-validity,
;; comparison, region, linkedness, constancy, and loop-prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sslpg2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sslpg2-address-base (address)
  (car address))

(defun sslpg2-address-offset (address)
  (cdr address))

(defun sslpg2-shift (address amount)
  (cons
   (sslpg2-address-base address)
   (+ (sslpg2-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region, logical
;; strlen, logical strncmp, C integer conversions, linkedness, and constancy
;; symbols.

(defstub sslpg2-character-memory (address) t)
(defstub sslpg2-allocation (index) t)
(defstub sslpg2-region (base) t)
(defstub sslpg2-l-strlen (address) t)
(defstub sslpg2-l-strncmp (left right count) t)
(defstub sslpg2-to-uint32 (value) t)
(defstub sslpg2-to-sint32 (value) t)
(defstub sslpg2-to-uint64 (value) t)
(defstub sslpg2-to-sint64 (value) t)
(defstub sslpg2-linked-op () t)
(defstub sslpg2-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sslpg2-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (sslpg2-address-p address)
      (and
       (integerp
        (sslpg2-character-memory address))
       (integerp
        (sslpg2-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sslpg2-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sslpg2-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sslpg2-to-uint32 value))
       (integerp
        (sslpg2-to-sint32 value))
       (integerp
        (sslpg2-to-uint64 value))
       (integerp
        (sslpg2-to-sint64 value))))
     (implies
      (and
       (sslpg2-address-p left)
       (sslpg2-address-p right)
       (integerp count))
      (integerp
       (sslpg2-l-strncmp left right count))))))

(defun sslpg2-linked-p ()
  (if (sslpg2-linked-op) t nil))

(defun sslpg2-sconst-p ()
  (if (sslpg2-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sslpg2-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sslpg2-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sslpg2-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun sslpg2-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun sslpg2-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by logical strlen and logical strncmp.

(defun-sk sslpg2-to-uint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslpg2-is-uint32-p
       (sslpg2-to-uint32 value))
      (implies
       (sslpg2-is-uint32-p value)
       (equal
        (sslpg2-to-uint32 value)
        value))
      (equal
       (sslpg2-to-uint32
        (sslpg2-to-uint32 value))
       (sslpg2-to-uint32 value))))))

(defun-sk sslpg2-to-sint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslpg2-is-sint32-p
       (sslpg2-to-sint32 value))
      (implies
       (sslpg2-is-sint32-p value)
       (equal
        (sslpg2-to-sint32 value)
        value))
      (equal
       (sslpg2-to-sint32
        (sslpg2-to-sint32 value))
       (sslpg2-to-sint32 value))))))

(defun-sk sslpg2-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslpg2-is-uint64-p
       (sslpg2-to-uint64 value))
      (implies
       (sslpg2-is-uint64-p value)
       (equal
        (sslpg2-to-uint64 value)
        value))
      (equal
       (sslpg2-to-uint64
        (sslpg2-to-uint64 value))
       (sslpg2-to-uint64 value))))))

(defun-sk sslpg2-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sslpg2-is-sint64-p
       (sslpg2-to-sint64 value))
      (implies
       (sslpg2-is-sint64-p value)
       (equal
        (sslpg2-to-sint64 value)
        value))
      (equal
       (sslpg2-to-sint64
        (sslpg2-to-sint64 value))
       (sslpg2-to-sint64 value))))))

;; Exact Cint.proj_int32 and Cint.proj_int64 cross-projection laws.

(defun-sk sslpg2-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (sslpg2-to-sint32
        (sslpg2-to-uint32 value))
       (sslpg2-to-sint32 value))
      (equal
       (sslpg2-to-sint64
        (sslpg2-to-uint64 value))
       (sslpg2-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sslpg2-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sslpg2-address-base address))
    (<= 0
        (sslpg2-address-offset address))
    (<=
     (+ (sslpg2-address-offset address)
        length)
     (sslpg2-allocation
      (sslpg2-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its null terminator remains an
;; internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sslpg2-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sslpg2-is-sint8-p
       (sslpg2-character-memory
        (sslpg2-shift address position)))))))

(defun-sk sslpg2-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sslpg2-character-memory
       (sslpg2-shift address index))
      0)
     (sslpg2-is-uint64-p index)
     (sslpg2-valid-rw-p
      (sslpg2-shift address 0)
      (+ 1 index))
     (sslpg2-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sslpg2-strlen-laws-p ()
  (forall (address)
    (implies
     (sslpg2-address-p address)
     (and
      (if
          (equal
           (sslpg2-character-memory
            (sslpg2-shift address 0))
           0)
          (equal
           (sslpg2-l-strlen address)
           0)
        (equal
         (sslpg2-to-uint64
          (+ 1
             (sslpg2-l-strlen
              (sslpg2-shift address 1))))
         (sslpg2-l-strlen address)))
      (sslpg2-is-uint64-p
       (sslpg2-l-strlen address))))))

;; Universal closures of A_StrnCmp.fix_l_strncmp_2' and Q_TL_strncmp_2'.

(defun-sk sslpg2-strncmp-laws-p ()
  (forall (left right count)
    (implies
     (and
      (sslpg2-address-p left)
      (sslpg2-address-p right)
      (integerp count))
     (and
      (if
          (equal count 0)
          (equal
           (sslpg2-l-strncmp left right count)
           0)
        (if
            (equal
             (sslpg2-character-memory
              (sslpg2-shift right 0))
             (sslpg2-character-memory
              (sslpg2-shift left 0)))
            (if
                (equal
                 (sslpg2-character-memory
                  (sslpg2-shift left 0))
                 0)
                (equal
                 (sslpg2-l-strncmp left right count)
                 0)
              (equal
               (sslpg2-l-strncmp
                (sslpg2-shift left 1)
                (sslpg2-shift right 1)
                (sslpg2-to-uint64 (- count 1)))
               (sslpg2-l-strncmp left right count)))
          (equal
           (sslpg2-to-sint32
            (-
             (sslpg2-character-memory
              (sslpg2-shift left 0))
             (sslpg2-character-memory
              (sslpg2-shift right 0))))
           (sslpg2-l-strncmp left right count))))
      (sslpg2-is-sint32-p
       (sslpg2-l-strncmp left right count))))))

(defun sslpg2-strnequal-p (left right count)
  (equal
   (sslpg2-l-strncmp left right count)
   0))

;; The source prefix hypothesis retains its universal quantifier over every
;; mathematical integer and its original nonnegative and strict upper bounds.

(defun-sk sslpg2-prefix-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (equal
        (sslpg2-character-memory
         (sslpg2-shift left position))
        (sslpg2-character-memory
         (sslpg2-shift right position))))))))

(defun-sk
    ntp4vc-sysfs-streq-loop-inv-preserved-goal2-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (sslpg2-address-p a1)
     (integerp i)
     (sslpg2-address-p a)
     (sslpg2-function-types-p)
     (sslpg2-to-uint32-laws-p)
     (sslpg2-to-sint32-laws-p)
     (sslpg2-to-uint64-laws-p)
     (sslpg2-to-sint64-laws-p)
     (sslpg2-signed-unsigned-projection-laws-p)
     (sslpg2-strlen-laws-p)
     (sslpg2-strncmp-laws-p))
    (let*
        ((a2
          (sslpg2-shift a1 i))
         (x
          (sslpg2-character-memory a2))
         (a3
          (sslpg2-shift a i))
         (x1
          (sslpg2-character-memory a3))
         (x2
          (+ 1 i)))
      (implies
       (and
        (not (equal x 0))
        (equal x x1)
        (<= i
            (sslpg2-l-strlen a))
        (<= i
            (sslpg2-l-strlen a1))
        (<=
         (sslpg2-region
          (sslpg2-address-base a))
         0)
        (<=
         (sslpg2-region
          (sslpg2-address-base a1))
         0)
        (sslpg2-linked-p)
        (sslpg2-sconst-p)
        (sslpg2-is-uint64-p i)
        (sslpg2-valid-string-p a)
        (sslpg2-valid-string-p a1)
        (sslpg2-strnequal-p a1 a i)
        (sslpg2-is-sint8-p x1)
        (sslpg2-is-sint8-p x)
        (sslpg2-valid-string-p a3)
        (sslpg2-valid-string-p a2)
        (sslpg2-prefix-equal-before-p
         a1 a i))
       (equal
        x2
        (sslpg2-to-uint64 x2)))))))

(value-triple :itpeval-statement-checked)

:q
