for mode = 0:1
    if mode == 0
        P = homo_lyap0;
        k=k0;
        lies = lies0;
        ss = stable0;
        crosses = crosses0;
    else
        P = homo_lyap1;
        k=k1;
        lies = lies1;
        ss = stable1;
        crosses = crosses1;
    end
    
    N = size(P, 1);
    translate_eq_point = [eye(N), -ss; zeros(1,N), 1];
    new_P = [P, zeros(N,1); zeros(1,N), 0];
    P_final = translate_eq_point' * new_P * translate_eq_point;
    
    if ~((norm([ss;1]' * P_final * [ss;1]) < 1e-5))
        disp("ERROR: ~(norm([ss;1]' * P_final * [ss;1]) < 1e-5)")
    end
    
    H = (-1)^mode * switching_pred;

    vol = truncated_ellipsoid_volume(P_final, k, H)
    
    vol_total = compute_volume(P_final, k)

    if ~((vol_total - vol)/vol_total >= - 1e-6)
        disp("ERROR: ~((vol_total - vol)/vol_total >= - 1e-6)")
    end
    if crosses == 0 
        
        if lies == mode && ~(abs((vol_total -vol)/vol_total) < 1e-6)
            disp("ERROR: lies == mode & ~(abs((vol_total -vol)/vol_total) < 1e-6)")
        end

        if lies ~= mode && ~(abs(vol) < 1e-6)
            disp("ERROR: lies ~= mode && ~(abs(vol) < 1e-6)")
        end
    else
        if ~(vol < vol_total)
            disp(~(vol < vol_total))
        end
        if lies == mode && ~(vol_total >= vol/2 - 1e-6)
            disp("ERROR: lies == mode && ~(vol_total >= vol/2 - 1e-6)")
        end
        if lies ~= mode && ~(vol < vol_total/2 + 1e-6)
            disp("ERROR: ~(vol < vol_total/2 + 1e-6)")
        end
        
    end
end