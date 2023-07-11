for mode = 0:1
    if mode == 0
        A=A0;
        P = homo_lyap0;
        k=k0;
        lies = lies0;
        ss = stable0;
        crosses = crosses0;
    else
        P = homo_lyap1;
        A=A1;
        k=k1;
        lies = lies1;
        ss = stable1;
        crosses = crosses1;
    end
    
    N = size(P, 1);
    translate_eq_point = [eye(N), -ss; zeros(1,N), 1];
    new_P = [P, zeros(N,1); zeros(1,N), 0];
    P_final = translate_eq_point' * new_P * translate_eq_point; 
    [P2, change_basis]= diagonalize_pol_deg_2(P_final);
    H1 = switching_pred * change_basis;
    
    if crosses == 0
        P3=restric_to_hyperplane(P2, H1);
        DDD=diagonalize_pol_deg_2(P3);
        k_new = DDD(end,end);
        k - k_new

    else
        hA=H1(1:end-1) * change_basis(1:N,1:N)^(-1) * A * change_basis(1:N,1:N);
        P3=restric_to_cod2_hyperplane(P2, H1, [hA, 0]);
        DDD=diagonalize_pol_deg_2(P3);
        k_new = DDD(end,end);
        k - k_new
    end

    
end



