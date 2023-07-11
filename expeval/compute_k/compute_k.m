function compute_k(data_file)
load(data_file)
for mode = 0:1    
    if mode == 0
        A=A0;
        P = homo_lyap0;
%        lies = lies0;
        ss = stable0;
%         oldk=k0;
    else
        P = homo_lyap1;
        A=A1;
%        lies = lies1;
        ss = stable1;
%         oldk=k1;
    end
    
%     if lies ~= modex
%         k=0
%     else
        N = size(P, 1);
        translate_eq_point = [eye(N), -ss; zeros(1,N), 1];
        new_P = [P, zeros(N,1); zeros(1,N), 0];
        P_final = translate_eq_point' * new_P * translate_eq_point; 
        [P2, change_basis]= diagonalize_pol_deg_2(P_final);
        H1 = switching_pred * change_basis;
    
    %     We now check if the minimum is reached in the region that we want
    % to avoid or not (to find the value of crossing)
        P3=restric_to_hyperplane(P2, H1);
        P3A = P3(1:N-1,1:N-1);
        b = P3(1:N-1,N);
        c = P3(N,N);
        minimum_point_hyperplane = - P3A\b;
        k_hyperplane=[minimum_point_hyperplane;1]'*P3*[minimum_point_hyperplane;1];
        h1 = H1(1:N);
        c1 = -H1(N+1);
        [~, max_ind] = max(abs(h1));
        indices=1:N;
        indices(max_ind)=[];
        min_p_hyp_all_coord=[zeros(N,1);1];
        min_p_hyp_all_coord(indices)=minimum_point_hyperplane;
        l=H1*min_p_hyp_all_coord;
        min_p_hyp_all_coord(max_ind) = -l/H1(max_ind);
        assert(abs(H1*min_p_hyp_all_coord)<1e-14)
        hA=H1(1:end-1) * change_basis(1:N,1:N)^(-1) * A * change_basis(1:N,1:N);
        if mode == 0
            if [hA, 0] * min_p_hyp_all_coord < 0
                crosses = 1;
            else
                crosses = 0;
            end
        else
            if [hA, 0] * min_p_hyp_all_coord > 0
                crosses = 1;
            else
                crosses = 0;
            end
        end

        if crosses == 0
            k = k_hyperplane;
        else
            P3=restric_to_cod2_hyperplane(P2, H1, [hA, 0]);
            DDD=diagonalize_pol_deg_2(P3);
            k = DDD(end,end);
        end

        if mode == 0
            k0 = k;
            save(data_file, 'k0', '-append')
        else
            k1 = k;
            save(data_file, 'k1', '-append')
        end

%     end
%     (k-oldk)/max(oldk,1)
end



