for mode = 0:1
    if mode == 0
        P = homo_lyap0;
        A = A0;
        B = B0;
        k=k0;
        assert(lies0 == 0)
        ss = stable0;
    else
        P = homo_lyap1;
        A = A1;
        B = B1;
        k=k1;
        assert(lies1 == 1)
        ss = stable1;
    end
    N = size(P, 1);
    eigP = eig(P);
    mu_1 = max(eigP);
    mu_n = min(eigP);
    radius_ball_inside_ellipsoid = sqrt(k/mu_1);
    h = switching_pred(1:N);
    c = -switching_pred(N+1);
    delta = abs(h*ss - c) / norm(h);
    alpha = min([radius_ball_inside_ellipsoid, delta]);
    beta = norm( A^(-1) * B);
    hA = h*A;
    sigma = (dot(hA,h)/norm(h)^2);
    g = hA - sigma*h;
    if norm(g)==0
        Robustness = delta/beta
    else
    mu = sqrt(mu_n/mu_1);
    gamma = norm(h*B)/norm(g);

    Robustness = min( [alpha*mu / (mu*(beta + gamma)+beta) , delta/beta] )
    end
end