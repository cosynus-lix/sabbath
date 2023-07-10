import numpy as np
from scipy import linalg
import picos as pc
from collections import namedtuple

HybridSystem = namedtuple('HybridSystem',
                          'Acs, bs, bprimes, Abars, Abarprimes, C')

# Class definitions

class LinearSystem():
    def __init__(self, A, B, C):
        # sanity checks
        if any(not isinstance(x, np.ndarray) for x in [A, B, C]):
            raise TypeError
        if len(A) != len(A[0]):
            raise ValueError("Matrix A is not square")
        if len(A[0]) != len(B):
            raise ValueError("Matrix B is not compatible with matrix A")
        if len(A) != len(C[0]):
            raise ValueError("Matrix C is not compatible with matrix A")

        self.A = A
        self.B = B
        self.C = C

        print (">> Read matrices")
        print (f"A size {len(A)}x{len(A[0])}")
        print (f"B size {len(B)}x{len(B[0])}")
        print (f"C size {len(C)}x{len(C[0])}")

    def dimension(self):
        # dimension of state space
        return len(self.A)

    def inputs(self):
        # number of inputs
        return len(self.B[0])

    def outputs(self):
        # number of outputs
        return len(self.C)

class PIController():
    def __init__(self, modes, conditions, KP, KI):
        # sanity checks
        if not isinstance(modes, int):
            raise TypeError
        if any( any(not isinstance(x, np.ndarray) for x in lst) for lst in [KP, KI]):
            raise TypeError
        if not (modes > 0):
            raise ValueError("At least one mode is expected")
        if len(conditions) != modes:
            raise ValueError("Conditions list has an incorrect length")
        if len(KP) != modes:
            raise ValueError("KP list has an incorrect length")
        if len(KI) != modes:
            raise ValueError("KI list has an incorrect length")
        r = len(KP[0])
        p = len(KP[0][0])
        if ((not all(len(x) == r for x in KP)) or
            (not all(len(x[0]) == p for x in KP))):
            raise ValueError("some matrix in KP is not of the right size")
        if ((not all(len(x) == r for x in KI)) or
            (not all(len(x[0]) == p for x in KI))):
            raise ValueError("some matrix in KI is not of the right size")
        #if not all(len(x) == p for x in conditions):
        #    raise ValueError("some condition vector is not of the right size")

        self.modes = modes
        self.conditions = conditions
        self.KP = KP
        self.KI = KI

        print (">> Controller matrices")
        print (f"KP1 size {len(KP[0])}x{len(KP[0][0])}")
        print (f"KP2 size {len(KP[1])}x{len(KP[1][0])}")
        print (f"KI1 size {len(KI[0])}x{len(KI[0][0])}")
        print (f"KI2 size {len(KI[1])}x{len(KI[1][0])}")

    def inputs(self):
        return len(self.KP[0])

#####
# FIXME quick attempt to normalize zeros.
def normalize(matrix):
    eps = np.finfo(np.float32).eps
    for i in range(len(matrix)):
        for j in range(len(matrix[0])):
            x = np.real(matrix[i][j])
            if (x < eps and x > -eps):
                matrix[i][j] = np.array(0.0, dtype='double')
#####

def reformulate(system, controller, refvalues):
    r = controller.inputs()
    A = system.A
    # remove the additional columns used for state disturbance
    # (these may have been introduced in the reduced matrices)
    B = system.B[:,:r]
    # update the B matrix in system
    system.B = B
    C = system.C
    n = system.dimension()
    p = system.outputs()

    # these parts are the same for each mode
    Ac_top = np.hstack([A, B])
    Cc = np.hstack([C, np.zeros([p,r])])

    AcList = []
    bList = []
    bprimeList = []

    # build Ac, b and b' matrices for each mode
    for mode in range(controller.modes):
        KP = controller.KP[mode]
        KI = controller.KI[mode]
        if (len(KP) != len(B[0])) or (len(KI) != len(B[0])):
            raise ValueError("The number of inputs in the controller matrices does not match the number of inputs in the given system")

        N = -1 * np.dot(KP, np.dot(C,A)) - np.dot(KI, C)
        M = -1 * np.dot(KP, np.dot(C,B))
        Ac_bot = np.hstack([N, M])
        Ac = np.vstack([Ac_top, Ac_bot])
        AcList.append(Ac)

        if len(refvalues) != p:
            raise ValueError("The number of reference values does not match the number of outputs in the given system")
        b_bot = np.dot(KI, refvalues)
        b = np.vstack([np.zeros([n,1]), b_bot])
        bList.append(b)

        # translated version of b (experimental)

        # Schur complement of block A in Ac
        S = M - np.dot(N, np.dot(np.linalg.inv(A), B))

        if mode == 0:
            S0inv = np.linalg.inv(S)
            b_prime = np.zeros([n+r, 1])
        else:
            # note: here we rely on the fact that S0inv has already been computed
            KIeff = KI - np.dot(np.dot(S, S0inv), controller.KI[0])

            # attempt to normalize KIeff'zeros.
            # currently disabled not to introduce spurious numerical errors.
            # normalize(KIeff)

            b_prime_bot = np.dot(KIeff, refvalues)
            b_prime = np.vstack([np.zeros([n,1]), b_prime_bot])

        bprimeList.append(b_prime)

    return (AcList, bList, bprimeList, Cc)


def check_stability(A):
    if not isinstance(A, np.ndarray):
        raise TypeError

    if (np.linalg.det(A) == 0):
        print ("[Warning] Matrix A is singular")

    eigenvalues = np.linalg.eig(A)[0]

    for x in eigenvalues:
        if (np.real(x) >= 0):
            print("[Warning] Found unstable eigenvalue:", x)

# -------------------------
# miniengine model

def get_miniengine_model():
    A = np.array([
        [-3.82987, -0.0418250, -1019.08],
        [0.284779, -1.76641, -349.432],
        [0, 0, -62.5000]
    ])

    B = np.array([
        [0],
        [0],
        [-0.790569],
    ])

    C = np.array([
        [0.00182850, 0, 0],
        [0.0000102703, 0.0000308108, 0]
    ])

    return LinearSystem(A,B,C)

def get_miniengine_controller():
    KP1 = np.array([
        [1, 0]
    ])
    KP2 = np.array([
        [0, 10]
    ])

    KI1 = np.array([
        [10, 0]
    ])
    KI2 = np.array([
        [0, 200]
    ])

    return PIController(2, [[], []], [KP1, KP2], [KI1, KI2])

def get_miniengine_references():
    return np.array([[0.5], [5]])

# -------------------------
# full model

def get_full_model():
    import scipy.io
    from pathlib import Path
    fname = str(Path(__file__).parent / 'simulink' / 'data_aero_02.mat')
    mat = scipy.io.loadmat(fname)
    A = np.array(mat['GA'], dtype='double')
    B = np.array(mat['GB'], dtype='double')
    C = np.array(mat['GC'], dtype='double')
    return LinearSystem(A, B, C)

def get_full_controller(kp2_gain=None):
    import scipy.io
    from pathlib import Path
    fname = str(Path(__file__).parent / 'simulink' / 'data_aero_02.mat')
    mat = scipy.io.loadmat(fname)

    # Important:
    # Couting from 0 index (while matlab starts from 1),
    # and modalities' indexes are swapped!
    #   mode 1 : y0 - r0 < switch_th
    #   mode 2 : y0 - r0 >= switch_th
    # hence: kp01 == Kp12 ...

    kp01 = mat['Kp12'][0][0] # 1
    kp02 = mat['Kp11'][0][0] # 0.1
    kp1 = mat['Kp2'][0][0] # 10
    kp2 = mat['Kp3'][0][0] # 0.5
    if kp2_gain is not None:
        kp1 *= kp2_gain

    ki01 = mat['Ki12'][0][0] # 10
    ki02 = mat['Ki11'][0][0] # 20
    ki1 = mat['Ki2'][0][0] # 100
    ki2 = mat['Ki3'][0][0] # 2

    KP1 = np.array([
        [kp01, 0, 0, 0],
        [0, 0, kp1, 0],
        [0, 0, 0, kp2]
    ], dtype='double')
    KP2 = np.array([
        [0, kp02, 0, 0],
        [0, 0, kp1, 0],
        [0, 0, 0, kp2]
    ], dtype='double')

    KI1 = np.array([
        [ki01, 0, 0, 0],
        [0, 0, ki1, 0],
        [0, 0, 0, ki2]
    ], dtype='double')
    KI2 = np.array([
        [0, ki02, 0, 0],
        [0, 0, ki1, 0],
        [0, 0, 0, ki2]
    ], dtype='double')

    return PIController(2, [[], []], [KP1, KP2], [KI1, KI2])

def get_full_references(use_zero_references=False):
    # TRY WITH NULL REFERENCES: this would not require to translate the matrix.
    if use_zero_references:
        return np.array([[0], [0], [0], [0]])
    return np.array([[0.5], [5], [-1], [20]])

# -------------------------
# reduced model

def get_reduced_model(n, round):
    from pathlib import Path
    fname = str(Path(__file__).parent / 'simulink' / 'data_aero_02_reduced_models_rounded.mat') \
        if round else \
        str(Path(__file__).parent / 'simulink' / 'data_aero_02_reduced_models.mat')
    import scipy.io
    mat = scipy.io.loadmat(fname)
    maybe_round = 'round_' if round else ''
    A = np.array(mat[f'GA_{maybe_round}{n}'], dtype='double')
    B = np.array(mat[f'GB_{maybe_round}{n}'], dtype='double')
    C = np.array(mat[f'GC_{maybe_round}{n}'], dtype='double')
    return LinearSystem(A, B, C)

def get_reduced_controller(size=None, round=None):
    # for size 3 with integer coefficients, we need to change the controller.
    kp2_gain = 0.8 if (round and size == 3) else 1
    return get_full_controller(kp2_gain)

def get_reduced_references(use_zero_references=False):
    return get_full_references(use_zero_references)

def select_model(args):
    def parse_references(references):
        assert not references is None

        references = references.strip()
        ref_strs = references.split(",")

        float_references = []
        for s in ref_strs:
            f_value = float(s.strip())
            float_references.append([f_value])
        return np.array(float_references)

    if args.size == 18:
        mod = get_full_model()
        ctl = get_full_controller()
        if args.references is None:
            refs = get_full_references()
        else:
            refs = parse_references(args.references)
            assert (len(refs) == len(get_full_references()))
    # elif args.miniengine:
    #     mod = get_miniengine_model()
    #     ctl = get_miniengine_controller()
    #     refs = get_miniengine_references()
    else:
        mod = get_reduced_model(args.size, args.round)
        ctl = get_reduced_controller(args.size, args.round)
        if args.references is None:
            refs = get_reduced_references()
        else:
            refs = parse_references(args.references)
            assert (len(refs) == len(get_reduced_references()))

    # Change of second column in matrix B in order to work with the old controller.
    change_B_matrix = True #not args.miniengine
    if change_B_matrix:
        u2_index = 1
        for i in range(len(mod.B)):
            mod.B[i, u2_index] = -mod.B[i, u2_index]

    return mod,ctl,refs

def get_ode_model_aux(mod, ctl, refs, verbose=False):
    (Acs, bs, bprimes, Cc) = reformulate(mod, ctl, refs)

    # reformulated matrices in w for each modality
    Abars = []
    Abarprimes = []

    for i in range(ctl.modes):
        if verbose:
            print("Checking stability for mode", i)
        check_stability(Acs[i])

        # in w coordinates
        Abar_i = np.vstack([
            np.hstack([Acs[i], bs[i]]),
            np.zeros([1, mod.dimension() + mod.inputs() + 1])
        ])
        Abars.append(Abar_i)

        # in w' coordinates: scaled to have equilibrium point in the origin
        Abar_i_centered = np.vstack([
            np.hstack([Acs[i], bprimes[i]]),
            np.zeros([1, mod.dimension() + mod.inputs() + 1])
        ])
        Abarprimes.append(Abar_i_centered)

    # Compute equilibrium points.
    # This was useful only to double check the simulations with simulink.
    try:
        for i in range(len(Acs)):
            eq = np.linalg.solve(Acs[i], bs[i])
            y = np.dot(Cc, eq)
            print (f"Equilibrium point mode {i}:", y)
    except np.linalg.LinAlgError:
        print ("[WARNING]: A is a singular matrix")

    return HybridSystem(Acs=Acs, bs=bs, Abars=Abars, Abarprimes=Abarprimes, bprimes=bprimes, C=Cc)

# ----------------------
# main function
def get_ode_model(args, verbose=False):
    mod,ctl,refs = select_model(args)
    return get_ode_model_aux(mod, ctl, refs, verbose)

